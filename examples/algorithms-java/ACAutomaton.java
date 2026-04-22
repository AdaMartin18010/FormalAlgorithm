/**
 * Aho-Corasick 自动机
 * 多模式字符串匹配
 * 构建: O(总模式长度), 查询: O(文本长度 + 匹配数)
 */
import java.util.*;

public class ACAutomaton {
    static class Node {
        Map<Character, Node> children = new HashMap<>();
        Node fail;
        List<String> output = new ArrayList<>();
    }

    private final Node root = new Node();

    public void insert(String word) {
        Node node = root;
        for (char ch : word.toCharArray()) {
            node = node.children.computeIfAbsent(ch, k -> new Node());
        }
        node.output.add(word);
    }

    public void build() {
        Queue<Node> q = new LinkedList<>();
        for (Node child : root.children.values()) {
            child.fail = root;
            q.add(child);
        }
        while (!q.isEmpty()) {
            Node curr = q.poll();
            for (Map.Entry<Character, Node> entry : curr.children.entrySet()) {
                char ch = entry.getKey();
                Node child = entry.getValue();
                Node fail = curr.fail;
                while (fail != null && !fail.children.containsKey(ch)) {
                    fail = fail.fail;
                }
                child.fail = (fail != null) ? fail.children.getOrDefault(ch, root) : root;
                child.output.addAll(child.fail.output);
                q.add(child);
            }
        }
    }

    public List<Map.Entry<Integer, List<String>>> search(String text) {
        List<Map.Entry<Integer, List<String>>> res = new ArrayList<>();
        Node node = root;
        for (int i = 0; i < text.length(); i++) {
            char ch = text.charAt(i);
            while (node != root && !node.children.containsKey(ch)) {
                node = node.fail;
            }
            node = node.children.getOrDefault(ch, root);
            if (!node.output.isEmpty()) {
                res.add(new AbstractMap.SimpleEntry<>(i, new ArrayList<>(node.output)));
            }
        }
        return res;
    }
}
