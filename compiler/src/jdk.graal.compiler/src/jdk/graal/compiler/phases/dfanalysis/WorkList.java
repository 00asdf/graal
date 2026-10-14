package jdk.graal.compiler.phases.dfanalysis;

import java.util.ArrayList;
import java.util.Map;
import java.util.Set;

import jdk.graal.compiler.graph.iterators.NodePredicate;
import jdk.graal.compiler.nodes.LoopBeginNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.cfg.HIRBlock;

public interface WorkList {
    void initialize(StructuredGraph graph, NodePredicate isStartingPoint);

    boolean hasNext();

    ValueNode next();

    void scheduleUsages(ValueNode node);

    void schedule(HIRBlock block, boolean inputEdgeBecameReachable);

    void schedule(ValueNode node);

    void unschedule(ArrayList<ValueNode> toUnschedule);

    void rescheduleLoopBegin(LoopBeginNode begin, boolean optimistic);

    boolean isOptimisticLoopPhi(ValueNode value);

    Map<ValueNode, Set<ValueNode>> patternInputs();

    default String prettyPrint() {
        return toString();
    }
}
