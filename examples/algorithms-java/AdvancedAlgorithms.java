/**
 * 高级算法实现
 * 包含: 模拟退火
 */
public class AdvancedAlgorithms {

    /**
     * 模拟退火求单变量函数最小值（离散版本）
     */
    public static double simulatedAnnealing(double[] arr, java.util.function.DoubleUnaryOperator neighborFn,
                                             java.util.function.DoubleUnaryOperator energyFn) {
        double current = arr[0];
        double currentEnergy = energyFn.applyAsDouble(current);
        double best = current;
        double bestEnergy = currentEnergy;
        double temp = 1.0;
        double coolingRate = 0.9999;
        for (int i = 0; i < 100000; i++) {
            double next = neighborFn.applyAsDouble(current);
            double nextEnergy = energyFn.applyAsDouble(next);
            double delta = nextEnergy - currentEnergy;
            if (delta < 0 || Math.random() < Math.exp(-delta / temp)) {
                current = next;
                currentEnergy = nextEnergy;
                if (currentEnergy < bestEnergy) {
                    best = current;
                    bestEnergy = currentEnergy;
                }
            }
            temp *= coolingRate;
        }
        return best;
    }
}
