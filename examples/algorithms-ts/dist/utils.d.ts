/**
 * 通用工具函数与测试基础设施
 * 提供严格的断言函数与辅助类型
 */
export type CompareFn<T> = (a: T, b: T) => number;
export type Predicate<T> = (value: T) => boolean;
/** 标准比较函数（适用于 number / string） */
export declare function defaultCompare<T>(a: T, b: T): number;
/** 交换数组中的两个元素 */
export declare function swap<T>(arr: T[], i: number, j: number): void;
/** 断言相等 */
export declare function assertEq<T>(actual: T, expected: T, message?: string): void;
/** 断言数组相等（按值比较） */
export declare function assertArrayEq<T>(actual: T[], expected: T[], message?: string): void;
/** 断言条件为真 */
export declare function assertTrue(condition: boolean, message?: string): void;
/** 断言函数抛出错误 */
export declare function assertThrows(fn: () => void, message?: string): void;
/** 运行测试套件 */
export declare function runTests(moduleName: string, tests: Record<string, () => void>): void;
//# sourceMappingURL=utils.d.ts.map