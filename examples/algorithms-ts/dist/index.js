"use strict";
/**
 * 算法库统一入口
 * 导出所有模块的公共接口
 */
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __exportStar = (this && this.__exportStar) || function(m, exports) {
    for (var p in m) if (p !== "default" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);
};
Object.defineProperty(exports, "__esModule", { value: true });
// 工具
__exportStar(require("./utils"), exports);
// 排序
__exportStar(require("./sorting"), exports);
// 数据结构
__exportStar(require("./data_structures"), exports);
// 搜索
__exportStar(require("./search"), exports);
// 图论
__exportStar(require("./graph"), exports);
// 动态规划
__exportStar(require("./dynamic_programming"), exports);
// 字符串
__exportStar(require("./string"), exports);
// 数论
__exportStar(require("./number_theory"), exports);
// 计算几何
__exportStar(require("./geometry"), exports);
// 树算法
__exportStar(require("./tree"), exports);
// 高级算法
__exportStar(require("./advanced"), exports);
//# sourceMappingURL=index.js.map