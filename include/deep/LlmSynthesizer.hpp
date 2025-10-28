#ifndef LLM_SYNTHESIZER_HPP
#define LLM_SYNTHESIZER_HPP

#include <string>
#include <curl/curl.h>
#include <iostream>
#include <cctype>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <vector>
#include <set>
#include <map>
#include <regex>
#include <unistd.h>
#include <limits.h>
#include <functional>
#include <algorithm>
#include <boost/lexical_cast.hpp>

// Include expr headers for full functionality
#include "ufo/Expr.hpp"
#include "deep/Horn.hpp"

class LlmSynthesizer {
private:
    std::string model_;
    std::string url_ = "http://localhost:1234/v1/chat/completions";
    int printLog = 0;
    expr::ExprSet previousGeneratedLemmas_;
    std::function<std::string(const std::string&)> transportOverride_;

public:
    struct GapPromptContext {
        std::string relationName;
        std::string triggerReason;
        expr::ExprSet learnedForRelation;
        expr::ExprSet failedCandidates;
        expr::ExprSet mbpGuards;
        expr::ExprSet phaseGuards;
        expr::Expr referenceCandidate;
        expr::ExprSet deferredCandidates;
        expr::ExprSet pendingLemmas;
        std::vector<std::string> diagnostics;
        unsigned attemptCount = 0;
        unsigned iteration = 0;
        unsigned cycle = 0;
    };

    // Constructor
    LlmSynthesizer(const std::string& model, int pl = 0) : model_(model), printLog(pl+1) {
        curl_global_init(CURL_GLOBAL_DEFAULT);
    }

    void setTransportOverride(std::function<std::string(const std::string&)> overrideFn) {
        transportOverride_ = std::move(overrideFn);
    }

    // Get the project root directory
    std::string getProjectRoot() {
        char exePath[PATH_MAX];
        ssize_t len = readlink("/proc/self/exe", exePath, sizeof(exePath) - 1);
        if (len == -1) {
            if(printLog >= 2) outs() << "Failed to get executable path" << std::endl;
            return "";
        }
        exePath[len] = '\0';
        
        std::string exeDir = std::string(exePath);
        // Remove the executable name
        size_t lastSlash = exeDir.find_last_of('/');
        if (lastSlash != std::string::npos) {
            exeDir = exeDir.substr(0, lastSlash);
        }
        
        // Navigate up from build/tools/deep to project root
        // build/tools/deep -> build/tools -> build -> project root
        for (int i = 0; i < 3; ++i) {
            size_t slash = exeDir.find_last_of('/');
            if (slash != std::string::npos) {
                exeDir = exeDir.substr(0, slash);
            } else {
                if(printLog >= 2) outs() << "Failed to navigate to project root" << std::endl;
                return "";
            }
        }
        
        return exeDir;
    }

    // Callback to collect response data
    static size_t WriteCallback(void *contents, size_t size, size_t nmemb, std::string *userp) {
        size_t total_size = size * nmemb;
        userp->append(static_cast<char *>(contents), total_size);
        return total_size;
    }

    // Escape a string for JSON
    std::string escapeJsonString(const std::string& str) {
        std::string escaped;
        escaped.reserve(str.size());
        for (char c : str) {
            switch (c) {
                case '"': escaped += "\\\""; break;
                case '\\': escaped += "\\\\"; break;
                case '\b': escaped += "\\b"; break;
                case '\f': escaped += "\\f"; break;
                case '\n': escaped += "\\n"; break;
                case '\r': escaped += "\\r"; break;
                case '\t': escaped += "\\t"; break;
                default:
                    if (static_cast<unsigned char>(c) < 32) {
                        char buf[8];
                        std::snprintf(buf, sizeof(buf), "\\u%04x", static_cast<unsigned char>(c));
                        escaped += buf;
                    } else {
                        escaped += c;
                    }
            }
        }
        return escaped;
    }

    // Build the JSON body for the request
    std::string buildJsonBody(const std::string& prompt) {
        std::string escapedPrompt = escapeJsonString(prompt);
        return R"({
            \"model\": \""" + model_ +
            R"("\",
            \"messages\": [{\"role\": \"user\", \"content\": \""" +
            escapedPrompt + R"("\"}],
            \"max_tokens\": 512,
            \"temperature\": 0.7,
            \"stream\": false
        })";
    }

    // Send the HTTP request and return the raw response
    std::string sendRequest(const std::string& json_body) {
        if(printLog >= 2) outs() << "Sending JSON: " << json_body << std::endl;
        CURL *curl = curl_easy_init();
        std::string response;
        if (curl) {
            struct curl_slist *headers = nullptr;
            headers = curl_slist_append(headers, "Content-Type: application/json");

            curl_easy_setopt(curl, CURLOPT_URL, url_.c_str());
            curl_easy_setopt(curl, CURLOPT_POSTFIELDS, json_body.c_str());
            curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);
            curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, WriteCallback);
            curl_easy_setopt(curl, CURLOPT_WRITEDATA, &response);

            CURLcode res = curl_easy_perform(curl);
            if (res != CURLE_OK) {
                if(printLog >= 2) outs() << "curl_easy_perform() failed: " << curl_easy_strerror(res) << std::endl;
                response.clear();
            } else {
                long http_code = 0;
                curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &http_code);
                if(printLog >= 2) outs() << "HTTP response code: " << http_code << std::endl;
                if (http_code != 200) {
                    outs() << "HTTP error: " << http_code << std::endl;
                    outs() << "Response body: " << response << std::endl;
                    response.clear();
                }
            }

            curl_slist_free_all(headers);
            curl_easy_cleanup(curl);
        }
        return response;
    }

    // Parse the raw JSON response to extract the content
    std::string parseResponse(const std::string& raw_response) {
        if (raw_response.empty()) {
            return "";
        }

        size_t key_pos = raw_response.find("\"content\"");
        if (key_pos == std::string::npos) {
            if(printLog >= 2) outs() << "Failed to find content key in response." << std::endl;
            return "";
        }

        size_t colon_pos = raw_response.find(":", key_pos + 9);
        if (colon_pos == std::string::npos) {
            if(printLog >= 2) outs() << "Failed to find colon after content key." << std::endl;
            return "";
        }

        size_t value_start = colon_pos + 1;
        while (value_start < raw_response.size() && std::isspace(static_cast<unsigned char>(raw_response[value_start]))) {
            ++value_start;
        }
        if (value_start >= raw_response.size() || raw_response[value_start] != '"') {
            if(printLog >= 2) outs() << "Failed to find start of content value." << std::endl;
            return "";
        }

        size_t content_start = value_start + 1;
        size_t content_end = content_start;
        bool escaped = false;
        while (content_end < raw_response.size()) {
            if (!escaped && raw_response[content_end] == '\\') {
                escaped = true;
                ++content_end;
                continue;
            }
            if (!escaped && raw_response[content_end] == '"') {
                break;
            }
            escaped = false;
            ++content_end;
        }
        if (content_end >= raw_response.size() || raw_response[content_end] != '"') {
            if(printLog >= 2) outs() << "Failed to find end of content." << std::endl;
            return "";
        }

        std::string content = raw_response.substr(content_start, content_end - content_start);

        size_t pos = 0;
        while (pos < content.size()) {
            if (content[pos] == '\\') {
                if (pos + 1 < content.size()) {
                    char next = content[pos + 1];
                    std::string repl;
                    if (next == 'n') repl = "\n";
                    else if (next == 't') repl = "\t";
                    else if (next == '"') repl = "\"";
                    else if (next == '\\') repl = "\\";
                    else if (next == '/') repl = "/";
                    else if (next == 'b') repl = "\b";
                    else if (next == 'f') repl = "\f";
                    else if (next == 'r') repl = "\r";
                    else {
                        pos += 2;
                        continue;
                    }
                    content.replace(pos, 2, repl);
                    pos += repl.size();
                } else {
                    break;
                }
            } else {
                ++pos;
            }
        }
        return content;
    }

    // Load a prompt template from file
    std::string loadTemplate(const std::string& templateName) {
        std::string projectRoot = getProjectRoot();
        if (projectRoot.empty()) {
            if(printLog >= 2) outs() << "Failed to determine project root directory" << std::endl;
            return "";
        }
                std::string templatePath = projectRoot + "/include/deep/prompts/" + templateName + ".txt";
        std::ifstream file(templatePath);
        if (!file.is_open()) {
            if(printLog >= 2) outs() << "Failed to open template file: " << templatePath << std::endl;
            return "";
        }
        std::string content((std::istreambuf_iterator<char>(file)), std::istreambuf_iterator<char>());
        file.close();
        return content;
    }

    // Fill in template placeholders with system information
    std::string fillTemplate(const std::string& templateContent,
                           const std::string& systemInfo,
                           const std::string& variables,
                           const std::string& previousLemmas,
                           const std::string& previousResponse) {
        std::string filled = templateContent;
        size_t pos;

        // Replace {SYSTEM_INFO}
        pos = filled.find("{SYSTEM_INFO}");
        if (pos != std::string::npos) {
            filled.replace(pos, 13, systemInfo);
        }

        // Replace {VARIABLES}
        pos = filled.find("{VARIABLES}");
        if (pos != std::string::npos) {
            filled.replace(pos, 11, variables);
        }

        // Replace {PREVIOUS_LEMMAS}
        pos = filled.find("{PREVIOUS_LEMMAS}");
        if (pos != std::string::npos) {
            filled.replace(pos, 17, previousLemmas);
        }

        // Replace {PREVIOUS_RESPONSE}
        pos = filled.find("{PREVIOUS_RESPONSE}");
        if (pos != std::string::npos) {
            filled.replace(pos, 19, previousResponse);
        }

        return filled;
    }

    // Load template and fill it in one step
    std::string preparePrompt(const std::string& templateName,
                            const std::string& systemInfo,
                            const std::string& variables,
                            const std::string& previousLemmas,
                            const std::string& previousResponse) {
        std::string templateContent = loadTemplate(templateName);
        if (templateContent.empty()) {
            return "";
        }
        return fillTemplate(templateContent, systemInfo, variables, previousLemmas, previousResponse);
    }

    // Extract system information from CHCs for prompt
    std::string extractSystemInfo(const ufo::CHCs& chcs) {
        std::stringstream ss;
        ss << "Constrained Horn Clauses System:\n";

        // Add CHC rules
        ss << "Rules (" << chcs.chcs.size() << " total):\n";
        for (size_t i = 0; i < chcs.chcs.size() && i < 10; ++i) { // Limit to first 10 for brevity
            ss << "  Rule " << i << ": " << chcs.chcs[i].srcRelation << " -> " << chcs.chcs[i].dstRelation << "\n";
        }
        if (chcs.chcs.size() > 10) {
            ss << "  ... and " << (chcs.chcs.size() - 10) << " more rules\n";
        }

        // Add array information
        if (chcs.hasAnyArrays) {
            ss << "System contains arrays.\n";
        }

        // Add query information
        if (chcs.hasQuery) {
            ss << "System has a query (safety property to verify).\n";
        }

        return ss.str();
    }

    // Extract variables information from CHCs
    std::string extractVariablesInfo(const ufo::CHCs& chcs) {
        std::stringstream ss;
        ss << "Variables by relation:\n";

        for (const auto& pair : chcs.invVars) {
            ss << "  " << pair.first << ": ";
            for (size_t i = 0; i < pair.second.size(); ++i) {
                if (i > 0) ss << ", ";
                ss << pair.second[i];
            }
            ss << "\n";
        }

        // Add learned lemmas if any
        if (!chcs.invVars.empty()) {
            ss << "\nNote: Variables are named with _FH_ prefix (e.g., _FH_0, _FH_1, etc.)\n";
        }

        ss << "\nUse only the variable names listed above when forming lemmas. Do not introduce any new variables.\n";

        return ss.str();
    }

    // Parse a prefix-form lemma string and convert to multiple Expr objects
    std::vector<expr::Expr> parseLemmasToExprs(const std::string& lemmaStr, const ufo::CHCs& chcs) {
        std::vector<expr::Expr> results;
        if (lemmaStr.empty()) {
            return results;
        }

        // Split the response into individual lines
        std::vector<std::string> lines;
        std::stringstream ss(lemmaStr);
        std::string line;
        while (std::getline(ss, line)) {
            line.erase(line.begin(), std::find_if(line.begin(), line.end(), [](unsigned char ch) {
                return !std::isspace(ch);
            }));
            line.erase(std::find_if(line.rbegin(), line.rend(), [](unsigned char ch) {
                return !std::isspace(ch);
            }).base(), line.end());

            if (!line.empty()) {
                lines.push_back(line);
            }
        }

        // Create a map from variable names to Expr objects
        std::map<std::string, expr::Expr> varMap;
        for (const auto& pair : chcs.invVars) {
            for (size_t i = 0; i < pair.second.size(); ++i) {
                std::string fhName = "_FH_" + std::to_string(i);
                varMap[fhName] = pair.second[i];

                std::string originalName;
                try {
                    originalName = boost::lexical_cast<std::string>(pair.second[i]);
                } catch (...) {
                    originalName.clear();
                }

                if (!originalName.empty()) {
                    auto trim = [](std::string& s) {
                        s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](unsigned char ch) { return !std::isspace(ch); }));
                        s.erase(std::find_if(s.rbegin(), s.rend(), [](unsigned char ch) { return !std::isspace(ch); }).base(), s.end());
                    };

                    trim(originalName);
                    if (!originalName.empty() && originalName.front() == '|' && originalName.back() == '|') {
                        originalName = originalName.substr(1, originalName.size() - 2);
                        trim(originalName);
                    }

                    if (!originalName.empty() && originalName.find_first_of(" ()") == std::string::npos) {
                        varMap[originalName] = pair.second[i];
                    }
                }
            }
        }

        for (const auto& singleLemma : lines) {
            expr::Expr result = parseParenthesizedExpression(singleLemma, chcs.m_efac, varMap);
            if (result) {
                results.push_back(result);
            }
        }

        return results;
    }

    // Parse a prefix-form lemma string and convert to Expr
    expr::Expr parseLemmaToExpr(const std::string& lemmaStr, const ufo::CHCs& chcs) {
        if(printLog >= 2) outs() << "Parsing lemma response: " << lemmaStr << std::endl;

        auto results = parseLemmasToExprs(lemmaStr, chcs);
        if (!results.empty()) {
            return results.front();
        }

        if(printLog >= 2) outs() << "Failed to parse any valid lemma from response" << std::endl;

        if (!chcs.invVars.empty()) {
            auto& invVars = chcs.invVars.begin()->second;
            if (!invVars.empty()) {
                return expr::mk<expr::op::GEQ>(invVars[0], expr::mkTerm<mpz_class>(0, chcs.m_efac));
            }
        }

        return expr::Expr();
    }

    // Parse parenthesized expressions like (>=_FH_0 0) or ((_FH_0+(-1*_FH_1))>=-5000)
    expr::Expr parseParenthesizedExpression(const std::string& expr, expr::ExprFactory& efac,
                                    const std::map<std::string, expr::Expr>& varMap) {
        std::string clean = expr;

        // Remove outer parentheses if present
        if (clean.size() >= 2 && clean[0] == '(' && clean.back() == ')') {
            clean = clean.substr(1, clean.size() - 2);
        }

        auto trim = [](std::string& s) {
            s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](unsigned char ch) { return !std::isspace(ch); }));
            s.erase(std::find_if(s.rbegin(), s.rend(), [](unsigned char ch) { return !std::isspace(ch); }).base(), s.end());
        };

        trim(clean);
        if (clean.empty()) {
            if(printLog >= 2) outs() << "Cannot parse empty expression" << std::endl;
            return expr::Expr();
        }

        std::string op;
        std::string rest;

        size_t firstSpace = clean.find(' ');
        if (firstSpace != std::string::npos) {
            op = clean.substr(0, firstSpace);
            rest = clean.substr(firstSpace + 1);
            trim(rest);
        } else {
            static const std::vector<std::string> infixOps = {">=", "<=", "==", "!=", ">", "<", "="};
            size_t foundPos = std::string::npos;
            std::string foundOp;
            for (const auto& candidate : infixOps) {
                size_t pos = clean.find(candidate);
                if (pos != std::string::npos) {
                    foundPos = pos;
                    foundOp = candidate;
                    break;
                }
            }

            if (foundPos == std::string::npos) {
                if(printLog >= 2) outs() << "No operator found in: " << clean << std::endl;
                return expr::Expr();
            }

            op = foundOp;
            std::string lhs = clean.substr(0, foundPos);
            std::string rhs = clean.substr(foundPos + foundOp.size());
            trim(lhs);
            trim(rhs);
            rest = lhs + " " + rhs;
        }

        if (op == ">=") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::GEQ>(a, b); }, varMap);
        } else if (op == "<=") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::LEQ>(a, b); }, varMap);
        } else if (op == ">") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::GT>(a, b); }, varMap);
        } else if (op == "<") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::LT>(a, b); }, varMap);
        } else if (op == "=" || op == "==") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::EQ>(a, b); }, varMap);
        } else if (op == "!=") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::NEQ>(a, b); }, varMap);
        } else if (op == "+") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::PLUS>(a, b); }, varMap);
        } else if (op == "-") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::MINUS>(a, b); }, varMap);
        } else if (op == "*") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::MULT>(a, b); }, varMap);
        } else if (op == "=>" || op == "implies") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::IMPL>(a, b); }, varMap);
        } else if (op == "and") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::AND>(a, b); }, varMap);
        } else if (op == "or") {
            return parseBinaryOp(op, rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::OR>(a, b); }, varMap);
        } else if (op == "not") {
            expr::Expr arg = parseOperand(rest, efac, varMap);
            if (arg) {
                return expr::mk<expr::op::NEG>(arg);
            }
            return expr::Expr();
        } else {
            if(printLog >= 2) outs() << "Unknown operator: " << op << std::endl;
            return expr::Expr();
        }
    }

    // Parse binary operations from the rest of the expression
    expr::Expr parseBinaryOp(const std::string& opName, const std::string& rest, expr::ExprFactory& efac,
                            std::function<expr::Expr(expr::Expr, expr::Expr)> opFunc,
                            const std::map<std::string, expr::Expr>& varMap) {
        // Find the two operands
        std::vector<std::string> operands;
        std::string current;
        int parenDepth = 0;

        for (size_t i = 0; i < rest.size(); ++i) {
            char c = rest[i];
            if (c == '(') {
                parenDepth++;
                current += c;
            } else if (c == ')') {
                parenDepth--;
                current += c;
            } else if (c == ' ' && parenDepth == 0) {
                if (!current.empty()) {
                    operands.push_back(current);
                    current.clear();
                }
            } else {
                current += c;
            }
        }

        if (!current.empty()) {
            operands.push_back(current);
        }

        if (operands.size() != 2) {
            if(printLog >= 2) outs() << "Expected 2 operands, got " << operands.size() << std::endl;
            return expr::Expr();
        }

        auto lhs = parseOperand(operands[0], efac, varMap);
        auto rhs = parseOperand(operands[1], efac, varMap);

        if (!lhs || !rhs) {
            return expr::Expr();
        }

        auto isBoolLiteral = [](const expr::Expr& e) {
            return expr::isOpX<expr::op::TRUE>(e) || expr::isOpX<expr::op::FALSE>(e);
        };

        bool lhsBool = isBoolLiteral(lhs);
        bool rhsBool = isBoolLiteral(rhs);

        if ((opName == ">=" || opName == ">" || opName == "<=" || opName == "<" ||
             opName == "+" || opName == "-" || opName == "*") && (lhsBool || rhsBool)) {
            if(printLog >= 2) outs() << "Boolean operand not allowed for operator " << opName << std::endl;
            return expr::Expr();
        }

        if ((opName == "=" || opName == "==" || opName == "!=") && (lhsBool != rhsBool)) {
            if(printLog >= 2) outs() << "Mismatched operand types for operator " << opName << std::endl;
            return expr::Expr();
        }

        return opFunc(lhs, rhs);
    }

    // Parse individual operands (variables, numbers, or subexpressions)
    expr::Expr parseOperand(const std::string& operand, expr::ExprFactory& efac,
                           const std::map<std::string, expr::Expr>& varMap) {
        std::string clean = operand;

        // Remove surrounding whitespace
        clean.erase(clean.begin(), std::find_if(clean.begin(), clean.end(), [](unsigned char ch) {
            return !std::isspace(ch);
        }));
        clean.erase(std::find_if(clean.rbegin(), clean.rend(), [](unsigned char ch) {
            return !std::isspace(ch);
        }).base(), clean.end());

        if (clean.empty()) return expr::Expr();

        // Check if it's a parenthesized subexpression
        if (clean.size() >= 2 && clean[0] == '(' && clean.back() == ')') {
            return parseParenthesizedExpression(clean, efac, varMap);
        }

        if (clean == "true") {
            return expr::mk<expr::op::TRUE>(efac);
        }
        if (clean == "false") {
            return expr::mk<expr::op::FALSE>(efac);
        }

        // Check if it's a variable (look it up in varMap)
        auto varIt = varMap.find(clean);
        if (varIt != varMap.end()) {
            return varIt->second;
        }

        auto isIdentifier = [](const std::string& name) {
            if (name.empty()) return false;
            unsigned char first = static_cast<unsigned char>(name[0]);
            if (!(std::isalpha(first) || first == '_')) return false;
            return std::all_of(name.begin() + 1, name.end(), [](unsigned char ch) {
                return std::isalnum(ch) || ch == '_' || ch == '\'';
            });
        };

        // Try to parse as integer literal
        try {
            int val = std::stoi(clean);
            return expr::mkTerm<mpz_class>(val, efac);
        } catch (...) {
            if (isIdentifier(clean)) {
                if(printLog >= 2) outs() << "Rejected lemma containing unknown variable: " << clean << std::endl;
            } else if(printLog >= 2) {
                outs() << "Failed to parse operand: " << clean << std::endl;
            }
            return expr::Expr();
        }
    }

    // Main method to synthesize response from prompt
    std::string synthesize(const std::string& prompt) {
        if (transportOverride_) {
            return transportOverride_(prompt);
        }
        std::string json_body = buildJsonBody(prompt);
        std::string raw_response = sendRequest(json_body);
        return parseResponse(raw_response);
    }

    // Generate multiple lemmas using the LLM
    std::vector<expr::Expr> generateLemmas(const ufo::CHCs& chcs,
                                          const expr::ExprSet& learnedLemmas,
                                          const expr::ExprSet& previousLemmas,
                                          const std::string& templateName = "basic_template") {
        // Extract system information
        std::string systemInfo = extractSystemInfo(chcs);
        std::string variablesInfo = extractVariablesInfo(chcs);

        // Add learned lemmas to system info
        if (!learnedLemmas.empty()) {
            std::stringstream ss;
            ss << systemInfo << "\nExisting learned lemmas:\n";
            size_t count = 0;
            size_t totalLearned = learnedLemmas.size();
            for (const auto& lemma : learnedLemmas) {
                if (count >= 5) { // Limit to 5 lemmas for brevity
                    size_t remaining = totalLearned > 5 ? (totalLearned - 5) : 0;
                    if (remaining > 0) {
                        ss << "  ... and " << remaining << " more\n";
                    }
                    break;
                }
                ss << "  " << lemma << "\n";
                count++;
            }
            systemInfo = ss.str();
        }

        auto appendLemmaSet = [](const expr::ExprSet& lemmas, const std::string& header) {
            std::stringstream ss;
            if (lemmas.empty()) {
                return std::string();
            }

            ss << header << "\n";
            size_t count = 0;
            size_t total = lemmas.size();
            for (const auto& lemma : lemmas) {
                if (count >= 5) {
                    size_t remaining = total > 5 ? (total - 5) : 0;
                    if (remaining > 0) {
                        ss << "  ... and " << remaining << " more\n";
                    }
                    break;
                }
                ss << "  " << lemma << "\n";
                ++count;
            }
            ss << "\n";
            return ss.str();
        };

        std::stringstream previousSection;
        previousSection << appendLemmaSet(previousLemmas, "Previously accepted lemmas:");
        previousSection << appendLemmaSet(previousGeneratedLemmas_, "Recent LLM lemmas:");

        std::string previousStr = previousSection.str();
        if (previousStr.empty()) {
            previousStr = "No previous lemmas provided.\n";
        }

        bool allowRetry = false;
        std::string retryContext;

        for (int attempt = 0; attempt < 2; ++attempt) {
            bool isRetry = (attempt == 1);
            if (isRetry && !allowRetry) {
                break;
            }

            std::string currentTemplate = isRetry ? "retry_template" : templateName;
            std::string prompt = preparePrompt(currentTemplate, systemInfo, variablesInfo, previousStr,
                                               isRetry ? retryContext : "");
            if (prompt.empty()) {
                if(printLog >= 2) outs() << "Failed to prepare " << currentTemplate << " prompt" << std::endl;
                break;
            }

            std::string response = synthesize(prompt);
            if (response.empty()) {
                if(printLog >= 2) outs() << "Empty response from LLM" << std::endl;
                if (!isRetry) {
                    allowRetry = true;
                    retryContext = "Previous response was empty. Please return valid lemmas.\n";
                    if(printLog >= 2) outs() << "Retrying with mitigation prompt" << std::endl;
                    continue;
                }
                break;
            }

            if(printLog >= 2) outs() << "LLM raw response: " << response << std::endl;

            std::vector<expr::Expr> lemmas = parseLemmasToExprs(response, chcs);
            std::vector<expr::Expr> uniqueLemmas;
            expr::ExprSet seenCurrentResponse;
            for (const auto& lemma : lemmas) {
                if (!lemma) {
                    continue;
                }

                if (learnedLemmas.count(lemma) || previousLemmas.count(lemma) || previousGeneratedLemmas_.count(lemma) ||
                    seenCurrentResponse.count(lemma)) {
                    if (printLog >= 2) {
                        outs() << "Skipping duplicate lemma: " << lemma << std::endl;
                    }
                    continue;
                }

                seenCurrentResponse.insert(lemma);
                uniqueLemmas.push_back(lemma);
            }

            if (!uniqueLemmas.empty()) {
                return uniqueLemmas;
            }

            if (!isRetry) {
                allowRetry = true;
                retryContext = "Previous response was malformed or unusable:\n" + response + "\n";
                if(printLog >= 2) outs() << "Response produced no usable lemmas; retrying with mitigation prompt" << std::endl;
                continue;
            }

            if(printLog >= 2) outs() << "Retry response still produced no usable lemmas" << std::endl;
            break;
        }

        if (printLog >= 2) outs() << "No new lemmas generated after retry attempts" << std::endl;
        return {};
    }

    // Generate a candidate lemma using LLM based on CHCs and learned lemmas
    expr::Expr generateLemma(const ufo::CHCs& chcs, const expr::ExprSet& learnedLemmas,
                           const std::string& templateName = "basic_template") {
        expr::ExprSet emptyPrevious;
        auto lemmas = generateLemmas(chcs, learnedLemmas, emptyPrevious, templateName);
        return lemmas.empty() ? expr::Expr() : lemmas.front();
    }

    // Generate multiple lemma candidates using different templates
    std::vector<expr::Expr> generateLemmaCandidates(const ufo::CHCs& chcs, const expr::ExprSet& learnedLemmas,
                                                   const std::vector<std::string>& templates = {"basic_template", "constraint_focused_template"}) {
        std::vector<expr::Expr> candidates;

        expr::ExprSet emptyPrevious;
        for (const auto& templateName : templates) {
            auto lemmas = generateLemmas(chcs, learnedLemmas, emptyPrevious, templateName);
            candidates.insert(candidates.end(), lemmas.begin(), lemmas.end());
        }

        return candidates;
    }

    void recordSampledLemma(const expr::Expr& lemma) {
        if (lemma) {
            previousGeneratedLemmas_.insert(lemma);
        }
    }

    std::vector<expr::Expr> generateGapLemmas(const ufo::CHCs& chcs,
                                             const GapPromptContext& context,
                                             const expr::ExprSet& previousLemmas,
                                             const std::string& templateName = "basic_template") {
        std::string systemInfo = extendSystemInfoWithLearned(chcs, context.learnedForRelation);
        if (!context.relationName.empty()) {
            systemInfo += "\nFocused relation: " + context.relationName + "\n";
        }
        if (!context.triggerReason.empty()) {
            systemInfo += "Trigger: " + context.triggerReason + "\n";
        }
        if (context.iteration > 0) {
            systemInfo += "Iteration: " + std::to_string(context.iteration) + "\n";
        }
        if (context.cycle > 0) {
            systemInfo += "Cycle index: " + std::to_string(context.cycle) + "\n";
        }
        if (context.attemptCount > 0) {
            systemInfo += "LLM attempts on relation: " + std::to_string(context.attemptCount) + "\n";
        }

        std::string variablesInfo = extractVariablesInfo(chcs);

        std::stringstream previousSection;
        previousSection << buildGapContextSection(context);
        previousSection << buildLemmaSetSection(previousLemmas, "Previously accepted lemmas:");
        previousSection << buildLemmaSetSection(previousGeneratedLemmas_, "Recent LLM lemmas:");

        std::string previousStr = previousSection.str();
        if (previousStr.empty()) {
            previousStr = "No previous lemmas provided.\n";
        }

        return generateLemmasFromSections(chcs,
                                          context.learnedForRelation,
                                          previousLemmas,
                                          systemInfo,
                                          variablesInfo,
                                          previousStr,
                                          templateName,
                                          "");
    }

private:
    std::string extendSystemInfoWithLearned(const ufo::CHCs& chcs,
                                            const expr::ExprSet& learnedLemmas) const {
        std::string systemInfo = extractSystemInfo(chcs);
        if (learnedLemmas.empty()) {
            return systemInfo;
        }

        std::stringstream ss;
        ss << systemInfo << "\nExisting learned lemmas:\n";
        size_t count = 0;
        size_t totalLearned = learnedLemmas.size();
        for (const auto& lemma : learnedLemmas) {
            if (count >= 5) {
                size_t remaining = totalLearned > 5 ? (totalLearned - 5) : 0;
                if (remaining > 0) {
                    ss << "  ... and " << remaining << " more\n";
                }
                break;
            }
            ss << "  " << exprToString(lemma) << "\n";
            ++count;
        }
        return ss.str();
    }

    std::string buildLemmaSetSection(const expr::ExprSet& lemmas,
                                     const std::string& header,
                                     size_t maxItems = 5) const {
        if (lemmas.empty()) {
            return std::string();
        }

        std::stringstream ss;
        ss << header << "\n";
        size_t count = 0;
        size_t total = lemmas.size();
        for (const auto& lemma : lemmas) {
            if (count >= maxItems) {
                size_t remaining = total > maxItems ? (total - maxItems) : 0;
                if (remaining > 0) {
                    ss << "  ... and " << remaining << " more\n";
                }
                break;
            }
            ss << "  " << exprToString(lemma) << "\n";
            ++count;
        }
        ss << "\n";
        return ss.str();
    }

    std::string exprToString(const expr::Expr& e) const {
        if (!e) {
            return "<null>";
        }
        try {
            return boost::lexical_cast<std::string>(e);
        } catch (...) {
            std::stringstream ss;
            ss << e;
            return ss.str();
        }
    }

    std::string buildGapContextSection(const GapPromptContext& context,
                                       size_t maxItems = 5) const {
        std::stringstream ss;
        if (context.referenceCandidate) {
            ss << "Reference candidate under analysis:\n  "
               << exprToString(context.referenceCandidate) << "\n\n";
        }
        if (!context.diagnostics.empty()) {
            ss << "Diagnostics:\n";
            for (const auto& line : context.diagnostics) {
                ss << "  - " << line << "\n";
            }
            ss << "\n";
        }
        ss << buildLemmaSetSection(context.failedCandidates, "Recently failed candidates:", maxItems);
        ss << buildLemmaSetSection(context.mbpGuards, "Relevant MBP guards:", maxItems);
        ss << buildLemmaSetSection(context.phaseGuards, "Phase guards:", maxItems);
        ss << buildLemmaSetSection(context.deferredCandidates, "Deferred candidates:", maxItems);
        ss << buildLemmaSetSection(context.pendingLemmas, "Pending LLM lemmas:", maxItems);
        return ss.str();
    }

    std::vector<expr::Expr> generateLemmasFromSections(
        const ufo::CHCs& chcs,
        const expr::ExprSet& learnedLemmas,
        const expr::ExprSet& previousLemmas,
        const std::string& systemInfo,
        const std::string& variablesInfo,
        const std::string& previousSection,
        const std::string& templateName,
        const std::string& previousResponse) {
        bool allowRetry = false;
        std::string retryContext;

        for (int attempt = 0; attempt < 2; ++attempt) {
            bool isRetry = (attempt == 1);
            if (isRetry && !allowRetry) {
                break;
            }

            std::string currentTemplate = isRetry ? "retry_template" : templateName;
            std::string prompt = preparePrompt(currentTemplate, systemInfo, variablesInfo, previousSection,
                                               isRetry ? retryContext : previousResponse);
            if (prompt.empty()) {
                if(printLog >= 2) outs() << "Failed to prepare " << currentTemplate << " prompt" << std::endl;
                break;
            }

            std::string response = synthesize(prompt);
            if (response.empty()) {
                if(printLog >= 2) outs() << "Empty response from LLM" << std::endl;
                if (!isRetry) {
                    allowRetry = true;
                    retryContext = "Previous response was empty. Please return valid lemmas.\n";
                    if(printLog >= 2) outs() << "Retrying with mitigation prompt" << std::endl;
                    continue;
                }
                break;
            }

            if(printLog >= 2) outs() << "LLM raw response: " << response << std::endl;

            std::vector<expr::Expr> lemmas = parseLemmasToExprs(response, chcs);
            std::vector<expr::Expr> uniqueLemmas;
            expr::ExprSet seenCurrentResponse;
            for (const auto& lemma : lemmas) {
                if (!lemma) {
                    continue;
                }

                if (learnedLemmas.count(lemma) || previousLemmas.count(lemma) || previousGeneratedLemmas_.count(lemma) ||
                    seenCurrentResponse.count(lemma)) {
                    if (printLog >= 2) {
                        outs() << "Skipping duplicate lemma: " << exprToString(lemma) << std::endl;
                    }
                    continue;
                }

                seenCurrentResponse.insert(lemma);
                uniqueLemmas.push_back(lemma);
            }

            if (!uniqueLemmas.empty()) {
                previousGeneratedLemmas_.insert(uniqueLemmas.begin(), uniqueLemmas.end());
                return uniqueLemmas;
            }

            if (!isRetry) {
                allowRetry = true;
                retryContext = "Previous response was malformed or unusable:\n" + response + "\n";
                if(printLog >= 2) outs() << "Response produced no usable lemmas; retrying with mitigation prompt" << std::endl;
                continue;
            }

            if(printLog >= 2) outs() << "Retry response still produced no usable lemmas" << std::endl;
            break;
        }

        if (printLog >= 2) outs() << "No new lemmas generated after retry attempts" << std::endl;
        return {};
    }
};

#endif // LLM_SYNTHESIZER_HPP
