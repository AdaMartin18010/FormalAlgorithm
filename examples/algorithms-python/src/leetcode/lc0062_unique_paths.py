"""
LeetCode 62. Unique Paths

There is a robot on an m x n grid. The robot is initially located at the
 top-left corner (i.e., grid[0][0]). The robot tries to move to the
 bottom-right corner (i.e., grid[m - 1][n - 1]). The robot can only move
down or right at any point in time.

Given the two integers m and n, return the number of possible unique paths
that the robot can take to reach the bottom-right corner.

Approach 1: 2D DP
- dp[i][j] = number of ways to reach cell (i, j)
- dp[i][j] = dp[i-1][j] + dp[i][j-1]
- Time: O(m*n), Space: O(m*n)

Approach 2: 1D rolling array
- Time: O(m*n), Space: O(n)

Approach 3: Combinatorics (not implemented here)
- C(m+n-2, m-1) = (m+n-2)! / ((m-1)! * (n-1)!)
- Time: O(min(m,n)), Space: O(1)
"""


class Solution:
    def uniquePaths(self, m: int, n: int) -> int:
        """
        1D rolling array DP.
        dp[j] represents the number of ways to reach the current row's column j.
        """
        dp = [1] * n  # First row: all 1s

        for i in range(1, m):
            for j in range(1, n):
                dp[j] += dp[j - 1]
            # dp[0] remains 1 for each row (only one way to reach first column)

        return dp[-1]


# --- Tests ---
if __name__ == "__main__":
    sol = Solution()
    assert sol.uniquePaths(3, 7) == 28
    assert sol.uniquePaths(3, 2) == 3
    assert sol.uniquePaths(1, 1) == 1
    assert sol.uniquePaths(1, 100) == 1
    assert sol.uniquePaths(100, 1) == 1
    assert sol.uniquePaths(2, 2) == 2
    print("All tests passed.")
