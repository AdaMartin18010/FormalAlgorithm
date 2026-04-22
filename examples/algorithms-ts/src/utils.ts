/**
 * 通用工具函数与测试基础设施
 * 提供严格的断言函数与辅助类型
 */

export type CompareFn<T> = (a: T, b: T) => number;
export type Predicate<T> = (value: T) => boolean;

/** 标准比较函数（适用于 number / string） */
export function defaultCompare<T>(a: T, b: T): number {
  if (a < b) return -1;
  if (a > b) return 1;
  return 0;
}

/** 交换数组中的两个元素 */
export function swap<T>(arr: T[], i: number, j: number): void {
  const temp = arr[i];
  arr[i] = arr[j];
  arr[j] = temp;
}

/** 断言相等 */
export function assertEq<T>(actual: T, expected: T, message?: string): void {
  const msg = message ?? `Expected ${expected}, got ${actual}`;
  if (actual !== expected) {
    throw new Error(`ASSERTION FAILED: ${msg}`);
  }
}

/** 断言数组相等（按值比较） */
export function assertArrayEq<T>(actual: T[], expected: T[], message?: string): void {
  const msg = message ?? `Array mismatch`;
  if (actual.length !== expected.length) {
    throw new Error(`ASSERTION FAILED: ${msg} (length ${actual.length} vs ${expected.length})`);
  }
  for (let i = 0; i < actual.length; i++) {
    if (actual[i] !== expected[i]) {
      throw new Error(`ASSERTION FAILED: ${msg} at index ${i}: expected ${expected[i]}, got ${actual[i]}`);
    }
  }
}

/** 断言条件为真 */
export function assertTrue(condition: boolean, message?: string): void {
  if (!condition) {
    throw new Error(`ASSERTION FAILED: ${message ?? "Expected true, got false"}`);
  }
}

/** 断言函数抛出错误 */
export function assertThrows(fn: () => void, message?: string): void {
  let threw = false;
  try {
    fn();
  } catch {
    threw = true;
  }
  if (!threw) {
    throw new Error(`ASSERTION FAILED: ${message ?? "Expected function to throw"}`);
  }
}

/** 运行测试套件 */
export function runTests(moduleName: string, tests: Record<string, () => void>): void {
  let passed = 0;
  let failed = 0;
  console.log(`\n[${moduleName}] Running ${Object.keys(tests).length} tests...`);
  for (const [name, fn] of Object.entries(tests)) {
    try {
      fn();
      passed++;
      console.log(`  PASS: ${name}`);
    } catch (err) {
      failed++;
      console.error(`  FAIL: ${name}: ${(err as Error).message}`);
    }
  }
  console.log(`[${moduleName}] Results: ${passed} passed, ${failed} failed`);
  if (failed > 0) {
    throw new Error(`${moduleName}: ${failed} test(s) failed`);
  }
}
