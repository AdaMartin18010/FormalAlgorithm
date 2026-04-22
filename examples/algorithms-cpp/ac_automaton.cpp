/**
 * ac_automaton.cpp - C++ AC自动机实现
 * 多模式字符串匹配
 */

#include <map>
#include <string>
#include <vector>
#include <queue>
#include <memory>

namespace ac {

struct Node {
    std::map<char, std::shared_ptr<Node>> children;
    std::shared_ptr<Node> fail;
    std::vector<std::string> output;
};

class AhoCorasick {
    std::shared_ptr<Node> root;
public:
    AhoCorasick() : root(std::make_shared<Node>()) {}

    void insert(const std::string& word) {
        auto node = root;
        for (char ch : word) {
            if (!node->children.count(ch)) {
                node->children[ch] = std::make_shared<Node>();
            }
            node = node->children[ch];
        }
        node->output.push_back(word);
    }

    void build() {
        std::queue<std::shared_ptr<Node>> q;
        for (auto& pair : root->children) {
            pair.second->fail = root;
            q.push(pair.second);
        }
        while (!q.empty()) {
            auto curr = q.front(); q.pop();
            for (auto& pair : curr->children) {
                char ch = pair.first;
                auto child = pair.second;
                auto fail = curr->fail;
                while (fail != nullptr && !fail->children.count(ch)) {
                    fail = fail->fail;
                }
                child->fail = (fail != nullptr) ? fail->children[ch] : root;
                if (child->fail == nullptr) child->fail = root;
                child->output.insert(child->output.end(), child->fail->output.begin(), child->fail->output.end());
                q.push(child);
            }
        }
    }

    std::vector<std::pair<int, std::vector<std::string>>> search(const std::string& text) {
        std::vector<std::pair<int, std::vector<std::string>>> res;
        auto node = root;
        for (size_t i = 0; i < text.size(); i++) {
            char ch = text[i];
            while (node != root && !node->children.count(ch)) {
                node = node->fail;
            }
            node = node->children.count(ch) ? node->children[ch] : root;
            if (!node->output.empty()) {
                res.push_back({(int)i, node->output});
            }
        }
        return res;
    }
};

} // namespace ac
