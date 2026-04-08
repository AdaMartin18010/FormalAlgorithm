//! 活动选择问题 - 贪心算法实现
//!
//! 活动选择问题是经典的贪心算法应用，目标是在有限资源（时间）内选择尽可能多的不冲突活动。


/// 活动结构
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Activity {
    /// 活动开始时间
    pub start: usize,
    /// 活动结束时间
    pub end: usize,
    /// 活动名称或标识（可选）
    pub name: Option<&'static str>,
}

impl Activity {
    /// 创建新活动
    ///
    /// # 示例
    ///
    /// ```
    /// use formal_algorithms::greedy_activity_selection::Activity;
    ///
    /// let activity = Activity::new(1, 4);
    /// assert_eq!(activity.start, 1);
    /// assert_eq!(activity.end, 4);
    /// ```
    pub fn new(start: usize, end: usize) -> Self {
        Activity {
            start,
            end,
            name: None,
        }
    }

    /// 创建带名称的活动
    ///
    /// # 示例
    ///
    /// ```
    /// use formal_algorithms::greedy_activity_selection::Activity;
    ///
    /// let activity = Activity::with_name(1, 4, "Meeting");
    /// assert_eq!(activity.name, Some("Meeting"));
    /// ```
    pub fn with_name(start: usize, end: usize, name: &'static str) -> Self {
        Activity {
            start,
            end,
            name: Some(name),
        }
    }

    /// 检查两个活动是否兼容（不重叠）
    ///
    /// # 示例
    ///
    /// ```
    /// use formal_algorithms::greedy_activity_selection::Activity;
    ///
    /// let a1 = Activity::new(1, 4);
    /// let a2 = Activity::new(4, 6);
    /// let a3 = Activity::new(3, 5);
    ///
    /// assert!(a1.is_compatible_with(&a2)); // 不重叠（边界接触）
    /// assert!(!a1.is_compatible_with(&a3)); // 重叠
    /// ```
    pub fn is_compatible_with(&self, other: &Activity) -> bool {
        self.end <= other.start || other.end <= self.start
    }

    /// 获取活动持续时间
    pub fn duration(&self) -> usize {
        self.end.saturating_sub(self.start)
    }
}

impl PartialOrd for Activity {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Activity {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.end.cmp(&other.end)
    }
}

/// 活动选择结果
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActivitySelectionResult {
    /// 选中的活动索引列表
    pub selected_indices: Vec<usize>,
    /// 选中的活动列表
    pub selected_activities: Vec<Activity>,
    /// 最多可选择的活动数量
    pub count: usize,
    /// 总占用时间
    pub total_duration: usize,
}

impl ActivitySelectionResult {
    fn new() -> Self {
        ActivitySelectionResult {
            selected_indices: Vec::new(),
            selected_activities: Vec::new(),
            count: 0,
            total_duration: 0,
        }
    }
}

/// 贪心活动选择算法
///
/// # 算法说明
///
/// 活动选择问题使用贪心策略求解：
/// 1. 将所有活动按结束时间升序排序
/// 2. 选择第一个活动（结束时间最早）
/// 3. 依次检查后续活动，选择开始时间不早于上一个选中活动结束时间的活动
///
/// 贪心选择性质：最早结束的活动一定包含在某个最优解中
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n log n)
///   - 排序：O(n log n)
///   - 选择：O(n)
/// - **空间复杂度**：O(n) - 存储结果
///
/// # 参数
///
/// * `activities` - 活动列表，每个活动包含开始和结束时间
///
/// # 返回值
///
/// 返回 `ActivitySelectionResult`，包含选中的活动信息
///
/// # 示例
///
/// ```
/// use formal_algorithms::greedy_activity_selection::{Activity, greedy_activity_selection};
///
/// let activities = vec![
///     Activity::new(1, 4),
///     Activity::new(3, 5),
///     Activity::new(0, 6),
///     Activity::new(5, 7),
///     Activity::new(3, 8),
///     Activity::new(5, 9),
///     Activity::new(6, 10),
///     Activity::new(8, 11),
///     Activity::new(8, 12),
///     Activity::new(2, 13),
///     Activity::new(12, 14),
/// ];
///
/// let result = greedy_activity_selection(&activities);
/// assert_eq!(result.count, 4);
/// ```
pub fn greedy_activity_selection(activities: &[Activity]) -> ActivitySelectionResult {
    let n = activities.len();
    if n == 0 {
        return ActivitySelectionResult::new();
    }

    // 创建带原始索引的活动列表
    let mut indexed_activities: Vec<(usize, &Activity)> = activities
        .iter()
        .enumerate()
        .collect();

    // 按结束时间升序排序
    indexed_activities.sort_by(|a, b| a.1.end.cmp(&b.1.end));

    let mut result = ActivitySelectionResult::new();

    // 选择第一个活动
    let (first_idx, first_activity) = indexed_activities[0];
    result.selected_indices.push(first_idx);
    result.selected_activities.push(*first_activity);
    result.total_duration = first_activity.duration();

    // 记录最后一个选中活动的结束时间
    let mut last_end = first_activity.end;

    // 贪心选择
    for (idx, activity) in indexed_activities.iter().skip(1) {
        if activity.start >= last_end {
            result.selected_indices.push(*idx);
            result.selected_activities.push(**activity);
            result.total_duration += activity.duration();
            last_end = activity.end;
        }
    }

    result.count = result.selected_indices.len();
    result
}

/// 带权重的活动选择问题（动态规划解法）
///
/// 当每个活动有不同的权重（价值）时，需要使用动态规划求解
///
/// # 参数
///
/// * `activities` - 带权重的活动列表 (start, end, weight)
///
/// # 返回值
///
/// 返回最大权重和选中的活动索引
///
/// # 示例
///
/// ```
/// use formal_algorithms::greedy_activity_selection::weighted_activity_selection;
///
/// let activities = vec![
///     (1, 4, 50),   // 活动1: 权重50
///     (3, 5, 20),   // 活动2: 权重20
///     (0, 6, 30),   // 活动3: 权重30
///     (5, 7, 60),   // 活动4: 权重60
///     (3, 8, 40),   // 活动5: 权重40
/// ];
///
/// let (max_weight, selected) = weighted_activity_selection(&activities);
/// assert_eq!(max_weight, 110); // 50 + 60 = 110
/// ```
pub fn weighted_activity_selection(activities: &[(usize, usize, i32)]) -> (i32, Vec<usize>) {
    let n = activities.len();
    if n == 0 {
        return (0, vec![]);
    }

    // 按结束时间排序，并记录原始索引
    let mut indexed: Vec<(usize, usize, usize, i32)> = activities
        .iter()
        .enumerate()
        .map(|(i, (s, e, w))| (i, *s, *e, *w))
        .collect();
    indexed.sort_by(|a, b| a.2.cmp(&b.2)); // 按结束时间排序

    // dp[i] = 前i个活动能获得的最大权重
    let mut dp = vec![0; n + 1];
    // choice[i] = 是否选择第i个活动
    let mut choice = vec![false; n];

    for i in 1..=n {
        let (_orig_idx, start, _end, weight) = indexed[i - 1];

        // 找到最后不冲突的活动
        let mut last_compatible = 0;
        for j in (0..i - 1).rev() {
            if indexed[j].2 <= start {
                last_compatible = j + 1;
                break;
            }
        }

        // 选择或不选择当前活动
        let with_current = dp[last_compatible] + weight;
        if with_current > dp[i - 1] {
            dp[i] = with_current;
            choice[i - 1] = true;
        } else {
            dp[i] = dp[i - 1];
        }
    }

    // 回溯找出选中的活动
    let mut selected = Vec::new();
    let mut i = n;
    while i > 0 {
        if choice[i - 1] {
            let (orig_idx, start, _, _) = indexed[i - 1];
            selected.push(orig_idx);

            // 跳到上一个兼容的活动
            let mut found = false;
            for j in (0..i - 1).rev() {
                if indexed[j].2 <= start {
                    i = j + 1;
                    found = true;
                    break;
                }
            }
            if !found {
                break;
            }
        } else {
            i -= 1;
        }
    }

    selected.reverse();
    (dp[n], selected)
}

/// 多会议室活动调度
///
/// 求至少需要多少个会议室才能安排所有活动
///
/// # 示例
///
/// ```
/// use formal_algorithms::greedy_activity_selection::min_meeting_rooms;
///
/// let activities = vec![
///     (0, 30),
///     (5, 10),
///     (15, 20),
/// ];
///
/// assert_eq!(min_meeting_rooms(&activities), 2);
/// ```
pub fn min_meeting_rooms(activities: &[(usize, usize)]) -> usize {
    if activities.is_empty() {
        return 0;
    }

    // 收集所有时间点和变化
    let mut events: Vec<(usize, i32)> = Vec::new(); // (时间, 变化: +1开始, -1结束)

    for (start, end) in activities {
        events.push((*start, 1));   // 活动开始，会议室+1
        events.push((*end, -1));    // 活动结束，会议室-1
    }

    // 按时间排序，相同时间先处理结束
    events.sort_by(|a, b| {
        if a.0 == b.0 {
            a.1.cmp(&b.1) // 结束(-1)在开始(1)之前
        } else {
            a.0.cmp(&b.0)
        }
    });

    let mut max_rooms = 0;
    let mut current_rooms = 0;

    for (_, delta) in events {
        current_rooms += delta;
        max_rooms = max_rooms.max(current_rooms);
    }

    max_rooms as usize
}

/// 验证活动选择结果是否有效
///
/// 检查选中的活动是否相互兼容
pub fn validate_selection(activities: &[Activity], selected_indices: &[usize]) -> bool {
    if selected_indices.len() <= 1 {
        return true;
    }

    // 获取选中的活动并按开始时间排序
    let mut selected: Vec<&Activity> = selected_indices
        .iter()
        .filter_map(|&idx| activities.get(idx))
        .collect();
    selected.sort_by(|a, b| a.start.cmp(&b.start));

    // 检查相邻活动是否兼容
    for i in 1..selected.len() {
        if selected[i - 1].end > selected[i].start {
            return false;
        }
    }

    true
}

/// 打印活动选择结果（用于调试）
pub fn print_selection(_activities: &[Activity], result: &ActivitySelectionResult) {
    println!("选中了 {} 个活动:", result.count);
    for (i, activity) in result.selected_activities.iter().enumerate() {
        let name = activity.name.unwrap_or("Unnamed");
        println!(
            "  活动 {}: {} [{} - {}] (持续 {} 单位)",
            result.selected_indices[i],
            name,
            activity.start,
            activity.end,
            activity.duration()
        );
    }
    println!("总持续时间: {}", result.total_duration);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_activities() {
        let activities: Vec<Activity> = vec![];
        let result = greedy_activity_selection(&activities);
        assert_eq!(result.count, 0);
        assert!(result.selected_activities.is_empty());
    }

    #[test]
    fn test_single_activity() {
        let activities = vec![Activity::new(1, 4)];
        let result = greedy_activity_selection(&activities);
        assert_eq!(result.count, 1);
        assert_eq!(result.selected_indices, vec![0]);
    }

    #[test]
    fn test_classic_example() {
        // CLRS教材经典例子
        let activities = vec![
            Activity::new(1, 4),
            Activity::new(3, 5),
            Activity::new(0, 6),
            Activity::new(5, 7),
            Activity::new(3, 8),
            Activity::new(5, 9),
            Activity::new(6, 10),
            Activity::new(8, 11),
            Activity::new(8, 12),
            Activity::new(2, 13),
            Activity::new(12, 14),
        ];

        let result = greedy_activity_selection(&activities);
        assert_eq!(result.count, 4);

        // 验证选中的活动是兼容的
        assert!(validate_selection(&activities, &result.selected_indices));
    }

    #[test]
    fn test_all_overlapping() {
        // 所有活动都重叠，只能选一个
        let activities = vec![
            Activity::new(1, 5),
            Activity::new(2, 6),
            Activity::new(3, 7),
            Activity::new(4, 8),
        ];

        let result = greedy_activity_selection(&activities);
        assert_eq!(result.count, 1);
    }

    #[test]
    fn test_no_overlap() {
        // 所有活动都不重叠，全部选中
        let activities = vec![
            Activity::new(1, 2),
            Activity::new(3, 4),
            Activity::new(5, 6),
            Activity::new(7, 8),
        ];

        let result = greedy_activity_selection(&activities);
        assert_eq!(result.count, 4);
    }

    #[test]
    fn test_activity_with_name() {
        let activity = Activity::with_name(1, 4, "Meeting");
        assert_eq!(activity.name, Some("Meeting"));
        assert_eq!(activity.start, 1);
        assert_eq!(activity.end, 4);
    }

    #[test]
    fn test_activity_compatibility() {
        let a1 = Activity::new(1, 4);
        let a2 = Activity::new(4, 6);
        let a3 = Activity::new(3, 5);

        assert!(a1.is_compatible_with(&a2)); // 边界接触，兼容
        assert!(!a1.is_compatible_with(&a3)); // 重叠，不兼容
        assert!(!a2.is_compatible_with(&a3)); // 重叠，不兼容
    }

    #[test]
    fn test_weighted_selection() {
        let activities = vec![
            (1, 4, 50),
            (3, 5, 20),
            (0, 6, 30),
            (5, 7, 60),
            (3, 8, 40),
        ];

        let (max_weight, selected) = weighted_activity_selection(&activities);
        assert_eq!(max_weight, 110); // 50 + 60 = 110
        assert!(selected.len() > 0);
    }

    #[test]
    fn test_min_meeting_rooms() {
        let activities = vec![
            (0, 30),
            (5, 10),
            (15, 20),
        ];
        assert_eq!(min_meeting_rooms(&activities), 2);

        let activities2 = vec![
            (7, 10),
            (2, 4),
        ];
        assert_eq!(min_meeting_rooms(&activities2), 1);

        let activities3: Vec<(usize, usize)> = vec![];
        assert_eq!(min_meeting_rooms(&activities3), 0);
    }

    #[test]
    fn test_validate_selection() {
        let activities = vec![
            Activity::new(1, 4),
            Activity::new(3, 5),
            Activity::new(5, 7),
        ];

        assert!(validate_selection(&activities, &[0, 2])); // 1-4 和 5-7 兼容
        assert!(!validate_selection(&activities, &[0, 1])); // 1-4 和 3-5 重叠
    }

    #[test]
    fn test_activity_duration() {
        let activity = Activity::new(1, 4);
        assert_eq!(activity.duration(), 3);

        let activity2 = Activity::new(5, 5);
        assert_eq!(activity2.duration(), 0);
    }

    #[test]
    fn test_weighted_selection_empty() {
        let activities: Vec<(usize, usize, i32)> = vec![];
        let (weight, selected) = weighted_activity_selection(&activities);
        assert_eq!(weight, 0);
        assert!(selected.is_empty());
    }

    #[test]
    fn test_same_end_time() {
        // 测试相同结束时间的活动
        let activities = vec![
            Activity::new(1, 5),
            Activity::new(2, 5),
            Activity::new(3, 5),
        ];

        let result = greedy_activity_selection(&activities);
        assert_eq!(result.count, 1);
    }
}
