"use strict";
/**
 * 统一测试运行器
 * 执行所有模块的内置测试
 */
Object.defineProperty(exports, "__esModule", { value: true });
const sorting_1 = require("../sorting");
const data_structures_1 = require("../data_structures");
const search_1 = require("../search");
const graph_1 = require("../graph");
const dynamic_programming_1 = require("../dynamic_programming");
const string_1 = require("../string");
const number_theory_1 = require("../number_theory");
const geometry_1 = require("../geometry");
const tree_1 = require("../tree");
const advanced_1 = require("../advanced");
function runAllTests() {
    console.log("==============================================");
    console.log("  TypeScript Algorithms Test Suite");
    console.log("==============================================");
    const start = Date.now();
    let totalPassed = 0;
    let totalFailed = 0;
    const modules = [
        { name: "Sorting", fn: sorting_1.runSortingTests },
        { name: "DataStructures", fn: data_structures_1.runDataStructureTests },
        { name: "Search", fn: search_1.runSearchTests },
        { name: "Graph", fn: graph_1.runGraphTests },
        { name: "DynamicProgramming", fn: dynamic_programming_1.runDynamicProgrammingTests },
        { name: "String", fn: string_1.runStringTests },
        { name: "NumberTheory", fn: number_theory_1.runNumberTheoryTests },
        { name: "Geometry", fn: geometry_1.runGeometryTests },
        { name: "Tree", fn: tree_1.runTreeTests },
        { name: "Advanced", fn: advanced_1.runAdvancedTests },
    ];
    for (const mod of modules) {
        try {
            mod.fn();
            totalPassed++;
        }
        catch {
            totalFailed++;
        }
    }
    const elapsed = Date.now() - start;
    console.log("\n==============================================");
    console.log(`  Total: ${modules.length} modules`);
    console.log(`  Passed: ${totalPassed}`);
    console.log(`  Failed: ${totalFailed}`);
    console.log(`  Time: ${elapsed}ms`);
    console.log("==============================================");
    if (totalFailed > 0) {
        process.exit(1);
    }
}
runAllTests();
//# sourceMappingURL=all_tests.js.map