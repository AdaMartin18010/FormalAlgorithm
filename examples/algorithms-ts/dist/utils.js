"use strict";
/**
 * 通用工具函数与测试基础设施
 * 提供严格的断言函数与辅助类型
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.defaultCompare = defaultCompare;
exports.swap = swap;
exports.assertEq = assertEq;
exports.assertArrayEq = assertArrayEq;
exports.assertTrue = assertTrue;
exports.assertThrows = assertThrows;
exports.runTests = runTests;
/** 标准比较函数（适用于 number / string） */
function defaultCompare(a, b) {
    if (a < b)
        return -1;
    if (a > b)
        return 1;
    return 0;
}
/** 交换数组中的两个元素 */
function swap(arr, i, j) {
    const temp = arr[i];
    arr[i] = arr[j];
    arr[j] = temp;
}
/** 断言相等 */
function assertEq(actual, expected, message) {
    const msg = message ?? `Expected ${expected}, got ${actual}`;
    if (actual !== expected) {
        throw new Error(`ASSERTION FAILED: ${msg}`);
    }
}
/** 断言数组相等（按值比较） */
function assertArrayEq(actual, expected, message) {
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
function assertTrue(condition, message) {
    if (!condition) {
        throw new Error(`ASSERTION FAILED: ${message ?? "Expected true, got false"}`);
    }
}
/** 断言函数抛出错误 */
function assertThrows(fn, message) {
    let threw = false;
    try {
        fn();
    }
    catch {
        threw = true;
    }
    if (!threw) {
        throw new Error(`ASSERTION FAILED: ${message ?? "Expected function to throw"}`);
    }
}
/** 运行测试套件 */
function runTests(moduleName, tests) {
    let passed = 0;
    let failed = 0;
    console.log(`\n[${moduleName}] Running ${Object.keys(tests).length} tests...`);
    for (const [name, fn] of Object.entries(tests)) {
        try {
            fn();
            passed++;
            console.log(`  PASS: ${name}`);
        }
        catch (err) {
            failed++;
            console.error(`  FAIL: ${name}: ${err.message}`);
        }
    }
    console.log(`[${moduleName}] Results: ${passed} passed, ${failed} failed`);
    if (failed > 0) {
        throw new Error(`${moduleName}: ${failed} test(s) failed`);
    }
}
//# sourceMappingURL=utils.js.map