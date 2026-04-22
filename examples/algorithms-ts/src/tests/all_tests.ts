/**
 * 统一测试运行器
 * 执行所有模块的内置测试
 */

import { runSortingTests } from "../sorting";
import { runDataStructureTests } from "../data_structures";
import { runSearchTests } from "../search";
import { runGraphTests } from "../graph";
import { runDynamicProgrammingTests } from "../dynamic_programming";
import { runStringTests } from "../string";
import { runNumberTheoryTests } from "../number_theory";
import { runGeometryTests } from "../geometry";
import { runTreeTests } from "../tree";
import { runAdvancedTests } from "../advanced";

function runAllTests(): void {
  console.log("==============================================");
  console.log("  TypeScript Algorithms Test Suite");
  console.log("==============================================");
  const start = Date.now();

  let totalPassed = 0;
  let totalFailed = 0;

  const modules = [
    { name: "Sorting", fn: runSortingTests },
    { name: "DataStructures", fn: runDataStructureTests },
    { name: "Search", fn: runSearchTests },
    { name: "Graph", fn: runGraphTests },
    { name: "DynamicProgramming", fn: runDynamicProgrammingTests },
    { name: "String", fn: runStringTests },
    { name: "NumberTheory", fn: runNumberTheoryTests },
    { name: "Geometry", fn: runGeometryTests },
    { name: "Tree", fn: runTreeTests },
    { name: "Advanced", fn: runAdvancedTests },
  ];

  for (const mod of modules) {
    try {
      mod.fn();
      totalPassed++;
    } catch {
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
