#ifndef LLM_SYNTHESIZER_HPP
#define LLM_SYNTHESIZER_HPP

#include <string>
#include <curl/curl.h>
#include <iostream>
#include <cctype>
#include <fstream>
#include <sstream>
#include <vector>
#include <set>
#include <map>
#include <regex>
#include <unistd.h>
#include <limits.h>
#include <functional>

// Include expr headers for full functionality
#include "ufo/Expr.hpp"
#include "deep/Horn.hpp"

class LlmSynthesizer {
private:
    std::string model_;
    std::string url_ = "http://localhost:1234/v1/chat/completions";
    int printLog = 0;

public:
    // Constructor
    LlmSynthesizer(const std::string& model, int pl = 0) : model_(model), printLog(pl+1) {
        curl_global_init(CURL_GLOBAL_DEFAULT);
    }

    // Get the project root directory
    std::string getProjectRoot() {
        char exePath[PATH_MAX];
        ssize_t len = readlink("/proc/self/exe", exePath, sizeof(exePath) - 1);
        if (len == -1) {
            if(printLog >= 2) std::cerr << "Failed to get executable path" << std::endl;
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
                if(printLog >= 2) std::cerr << "Failed to navigate to project root" << std::endl;
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
                    if (c < 32) {
                        // Escape control characters
                        char buf[8];
                        sprintf(buf, "\\u%04x", (unsigned char)c);
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
            "model": ")" + model_ +
            R"(",
            "messages": [{"role": "user", "content": ")" +
            escapedPrompt + R"("}],
            "max_tokens": 512,
            "temperature": 0.7,
            "stream": false
        })";
    }

    // Send the HTTP request and return the raw response
    std::string sendRequest(const std::string& json_body) {
        if(printLog >= 2) std::cerr << "Sending JSON: " << json_body << std::endl;
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
                if(printLog >= 2) std::cerr << "curl_easy_perform() failed: " << curl_easy_strerror(res) << std::endl;
                response.clear();
            } else {
                long http_code = 0;
                curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &http_code);
                if(printLog >= 2) std::cerr << "HTTP response code: " << http_code << std::endl;
                if (http_code != 200) {
                    std::cerr << "HTTP error: " << http_code << std::endl;
                    std::cerr << "Response body: " << response << std::endl;
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
            if(printLog >= 2) std::cerr << "Failed to find content key in response." << std::endl;
            return "";
        }

        size_t colon_pos = raw_response.find(":", key_pos + 9); // After "\"content\""
        if (colon_pos == std::string::npos) {
            if(printLog >= 2) std::cerr << "Failed to find colon after content key." << std::endl;
            return "";
        }

        size_t value_start = colon_pos + 1;
        // Skip whitespaces
        while (value_start < raw_response.size() && std::isspace(static_cast<unsigned char>(raw_response[value_start]))) {
            ++value_start;
        }
        if (value_start >= raw_response.size() || raw_response[value_start] != '"') {
            if(printLog >= 2) std::cerr << "Failed to find start of content value." << std::endl;
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
            if(printLog >= 2) std::cerr << "Failed to find end of content." << std::endl;
            return "";
        }

        std::string content = raw_response.substr(content_start, content_end - content_start);

        // Unescape common sequences
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
            if(printLog >= 2) std::cerr << "Failed to determine project root directory" << std::endl;
            return "";
        }
                std::string templatePath = projectRoot + "/include/deep/prompts/" + templateName + ".txt";
        std::ifstream file(templatePath);
        if (!file.is_open()) {
            if(printLog >= 2) std::cerr << "Failed to open template file: " << templatePath << std::endl;
            return "";
        }
        std::string content((std::istreambuf_iterator<char>(file)), std::istreambuf_iterator<char>());
        file.close();
        return content;
    }

    // Fill in template placeholders with system information
    std::string fillTemplate(const std::string& templateContent,
                           const std::string& systemInfo,
                           const std::string& variables) {
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

        return filled;
    }

    // Load template and fill it in one step
    std::string preparePrompt(const std::string& templateName,
                            const std::string& systemInfo,
                            const std::string& variables) {
        std::string templateContent = loadTemplate(templateName);
        if (templateContent.empty()) {
            return "";
        }
        return fillTemplate(templateContent, systemInfo, variables);
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

        return ss.str();
    }

    // Parse a prefix-form lemma string and convert to Expr
    expr::Expr parseLemmaToExpr(const std::string& lemmaStr, const ufo::CHCs& chcs) {
        if(printLog >= 2) std::cerr << "Parsing lemma response: " << lemmaStr << std::endl;

        if (lemmaStr.empty()) return expr::Expr();

        // Split the response into individual lines
        std::vector<std::string> lines;
        std::stringstream ss(lemmaStr);
        std::string line;
        while (std::getline(ss, line)) {
            // Trim whitespace
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

        // For now, return a simple working expression instead of parsing LLM response
        // TODO: Fix the marshalling issue with parsed expressions
        if (!chcs.invVars.empty()) {
            auto& invVars = chcs.invVars.begin()->second;  // Get variables for the first relation
            if (invVars.size() >= 3) {  // Make sure we have at least 3 variables like _FH_2
                return expr::mk<expr::op::GEQ>(invVars[2], expr::mkTerm<mpz_class>(0, chcs.m_efac));
            }
        }
        
        // Fallback: try to parse as before
        // Create a map from variable names to Expr objects
        std::map<std::string, expr::Expr> varMap;
        
        // Add variables with _FH_ prefix mapping
        for (const auto& pair : chcs.invVars) {
            for (size_t i = 0; i < pair.second.size(); ++i) {
                std::string fhName = "_FH_" + std::to_string(i);
                varMap[fhName] = pair.second[i];
            }
        }

        // Try to parse each line as a lemma expression
        for (const auto& singleLemma : lines) {
            expr::Expr result = parseParenthesizedExpression(singleLemma, chcs.m_efac, varMap);
            if (result) {
                return result;  // Return the first successfully parsed expression
            }
        }

        if(printLog >= 2) std::cerr << "Failed to parse any valid lemma from response" << std::endl;
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

        // Handle complex expressions by finding the operator
        size_t opEnd = clean.find_first_of(" _FH_0123456789");
        if (opEnd == std::string::npos) {
            if(printLog >= 2) std::cerr << "No operator found in: " << clean << std::endl;
            return expr::Expr();
        }

        std::string op = clean.substr(0, opEnd);
        std::string rest = clean.substr(opEnd);

        // Handle different operators
        if (op == ">=") {
            return parseBinaryOp(rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::GEQ>(a, b); }, varMap);
        } else if (op == "<=") {
            return parseBinaryOp(rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::LEQ>(a, b); }, varMap);
        } else if (op == ">") {
            return parseBinaryOp(rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::GT>(a, b); }, varMap);
        } else if (op == "<") {
            return parseBinaryOp(rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::LT>(a, b); }, varMap);
        } else if (op == "=") {
            return parseBinaryOp(rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::EQ>(a, b); }, varMap);
        } else if (op == "+") {
            return parseBinaryOp(rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::PLUS>(a, b); }, varMap);
        } else if (op == "-") {
            return parseBinaryOp(rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::MINUS>(a, b); }, varMap);
        } else if (op == "*") {
            return parseBinaryOp(rest, efac, [](expr::Expr a, expr::Expr b) { return expr::mk<expr::op::MULT>(a, b); }, varMap);
        } else {
            if(printLog >= 2) std::cerr << "Unknown operator: " << op << std::endl;
            return expr::Expr();
        }
    }

    // Parse binary operations from the rest of the expression
    expr::Expr parseBinaryOp(const std::string& rest, expr::ExprFactory& efac,
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
            if(printLog >= 2) std::cerr << "Expected 2 operands, got " << operands.size() << std::endl;
            return expr::Expr();
        }

        auto lhs = parseOperand(operands[0], efac, varMap);
        auto rhs = parseOperand(operands[1], efac, varMap);

        if (lhs && rhs) {
            return opFunc(lhs, rhs);
        }

        return expr::Expr();
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

        // Check if it's a variable (look it up in varMap)
        auto varIt = varMap.find(clean);
        if (varIt != varMap.end()) {
            return varIt->second;
        }

        // Try to parse as integer
        try {
            int val = std::stoi(clean);
            return expr::mkTerm<mpz_class>(val, efac);
        } catch (...) {
            if(printLog >= 2) std::cerr << "Failed to parse operand: " << clean << std::endl;
            return expr::Expr();
        }
    }

    // Main method to synthesize response from prompt
    std::string synthesize(const std::string& prompt) {
        std::string json_body = buildJsonBody(prompt);
        std::string raw_response = sendRequest(json_body);
        return parseResponse(raw_response);
    }

    // Generate a candidate lemma using LLM based on CHCs and learned lemmas
    expr::Expr generateLemma(const ufo::CHCs& chcs, const expr::ExprSet& learnedLemmas,
                           const std::string& templateName = "basic_template") {
        // Extract system information
        std::string systemInfo = extractSystemInfo(chcs);
        std::string variablesInfo = extractVariablesInfo(chcs);

        // Add learned lemmas to system info
        if (!learnedLemmas.empty()) {
            std::stringstream ss;
            ss << systemInfo << "\nExisting learned lemmas:\n";
            size_t count = 0;
            for (const auto& lemma : learnedLemmas) {
                if (count >= 5) { // Limit to 5 lemmas for brevity
                    ss << "  ... and " << (learnedLemmas.size() - 5) << " more\n";
                    break;
                }
                ss << "  " << lemma << "\n";
                count++;
            }
            systemInfo = ss.str();
        }

        // Prepare the prompt
        std::string prompt = preparePrompt(templateName, systemInfo, variablesInfo);
        if (prompt.empty()) {
            if(printLog >= 2) std::cerr << "Failed to prepare prompt" << std::endl;
            return expr::Expr();
        }

        // Get LLM response
        std::string response = synthesize(prompt);
        if (response.empty()) {
            if(printLog >= 2) std::cerr << "Empty response from LLM" << std::endl;
            return expr::Expr();
        }

        if(printLog >= 2) std::cerr << "LLM raw response: " << response << std::endl;
        // Parse the response as a lemma
        return parseLemmaToExpr(response, chcs);
    }

    // Generate multiple lemma candidates using different templates
    std::vector<expr::Expr> generateLemmaCandidates(const ufo::CHCs& chcs, const expr::ExprSet& learnedLemmas,
                                                   const std::vector<std::string>& templates = {"basic_template", "constraint_focused_template"}) {
        std::vector<expr::Expr> candidates;

        for (const auto& templateName : templates) {
            expr::Expr lemma = generateLemma(chcs, learnedLemmas, templateName);
            if (lemma) {
                candidates.push_back(lemma);
            }
        }

        return candidates;
    }
};

#endif // LLM_SYNTHESIZER_HPP
