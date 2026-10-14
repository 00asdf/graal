package jdk.graal.compiler.phases.dfanalysis;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;

import org.graalvm.collections.EconomicSet;

import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.graph.iterators.NodePredicate;
import jdk.graal.compiler.nodes.AbstractMergeNode;
import jdk.graal.compiler.nodes.LoopBeginNode;
import jdk.graal.compiler.nodes.LoopEndNode;
import jdk.graal.compiler.nodes.LoopExitNode;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.ValuePhiNode;
import jdk.graal.compiler.nodes.cfg.HIRBlock;
import jdk.graal.compiler.nodes.memory.MemoryKill;
import jdk.graal.compiler.util.EconomicHashMap;

public final class FullWorkList implements WorkList {

    @SuppressWarnings("deprecation")
    private static int[] calculatePrios(StructuredGraph graph) {
        var schedule = graph.getLastSchedule();
        var cfg = schedule.getCFG();
        int[] prios = new int[graph.nodeIdCount()];
        Map<HIRBlock, Integer> deepestPrio = EconomicHashMap.newIdentityMap();
        Arrays.fill(prios, -1);
        Queue<HIRBlock> workList = new ArrayDeque<>();

        // initialize
        {
            HIRBlock startBlock = cfg.getStartBlock();
            int depth = 0;
            for (var n : schedule.nodesFor(startBlock)) {
                prios[n.getId()] = depth++;
            }
            deepestPrio.put(startBlock, depth - 1);
            for (int i = 0; i < startBlock.getSuccessorCount(); i++) {
                workList.add(startBlock.getSuccessorAt(i));
            }
        }

        workLoop: while (!workList.isEmpty()) {
            HIRBlock block = workList.remove();
            if (deepestPrio.containsKey(block)) {
                // we already have a priority for this block
                continue workLoop;
            }

            int depth = 0;
            for (int i = 0; i < block.getPredecessorCount(); i++) {
                HIRBlock predecessor = block.getPredecessorAt(i);
                if (predecessor.isLoopEnd()) {
                    // ignore back edges in priority calculation
                    continue;
                }
                if (!deepestPrio.containsKey(predecessor)) {
                    // this block will come up later
                    continue workLoop;
                }
                depth = Math.max(depth, deepestPrio.get(predecessor));
            }

            if (block.getBeginNode() instanceof LoopExitNode exit) {
                for (LoopEndNode end : exit.loopBegin().loopEnds()) {
                    if (!deepestPrio.containsKey(cfg.blockFor(end))) {
                        // if we hit a loop end that has not been evaluated yet, we try again
                        // later
                        continue workLoop;
                    }
                    depth = Math.max(depth, deepestPrio.get(cfg.blockFor(end)));
                }
            }
            depth++;

            // now do node prios
            for (var n : schedule.nodesFor(block)) {
                prios[n.getId()] = depth++;
            }
            deepestPrio.put(block, depth - 1);

            for (int i = 0; i < block.getSuccessorCount(); i++) {
                workList.add(block.getSuccessorAt(i));
            }

            if (block.getEndNode() instanceof LoopEndNode end) {
                for (LoopExitNode exit : end.loopBegin().loopExits()) {
                    workList.add(cfg.blockFor(exit));
                }
            }
        }

        return prios;
    }

    private final EconomicSet<ValueNode> scheduled;
    private final EconomicSet<AbstractMergeNode> optimisticLoopBegins;
    private final PriorityQueue<PriorityElement> queue;
    private final int[] prios;

    private final Map<ValueNode, Set<ValueNode>> patternInputs;

    @Override
    public Map<ValueNode, Set<ValueNode>> patternInputs() {
        return patternInputs;
    }

    public FullWorkList(StructuredGraph graph) {
        this.scheduled = EconomicSet.create();
        this.optimisticLoopBegins = EconomicSet.create();
        this.queue = new PriorityQueue<>(Comparator.comparingLong(PriorityElement::priority));
        this.prios = calculatePrios(graph);
        patternInputs = new EconomicHashMap<>();
    }

    @Override
    public void initialize(StructuredGraph graph, NodePredicate isStartingPoint) {
        for (Node nd : graph.getNodes()) {
            if (nd instanceof ValueNode vn) {
                if (isStartingPoint.test(vn)) {
                    schedule(vn);
                }
            }
        }
    }

    @Override
    public boolean hasNext() {
        return !scheduled.isEmpty();
    }

    @Override
    public ValueNode next() {
        ValueNode nextNode = queue.remove().node();
        scheduled.remove(nextNode);
        if (nextNode instanceof LoopBeginNode loopBeginNode) {
            optimisticLoopBegins.remove(loopBeginNode);
        }
        return nextNode;
    }

    @Override
    public void scheduleUsages(ValueNode node) {
        boolean watchOutForMemory = MemoryKill.isMemoryKill(node);
        for (Node u : node.usages()) {
            if (u instanceof ValueNode value) {
                if (watchOutForMemory && DFAnalysis.isMemoryUsage(node, value)) {
                    // this node can have memory usages which we can not reason about
                    continue;
                }
                schedule(value);
            }
        }
    }

    @Override
    public void schedule(HIRBlock block, boolean inputEdgeBecameReachable) {
        if (block.getBeginNode() instanceof AbstractMergeNode merge) {
            schedule(merge);
        }
        if (inputEdgeBecameReachable) {
            // if an input edge became reachable, we need to schedule all inferences of this block
            for (InferredFactNode<?> iFact : block.getBeginNode().usages().filter(InferredFactNode.class)) {
                schedule(iFact);
            }
        }
        block.getBeginNode().usages().filter(InferredFactNode.class).forEach(this::schedule);
        // for control flow propagation we schedule the block's end
        schedule(block.getEndNode());
    }

    @Override
    public void schedule(ValueNode node) {
        if (node instanceof ValuePhiNode phi) {
            /*
             * We do not schedule PHIs directly, we rather schedule their associated MERGE node to
             * allow for full evaluation of all PHIs at the given merge at the same time.
             */
            schedule(phi.merge());
            return;
        }
        boolean newlyScheduled = scheduled.add(node);
        if (patternInputs.containsKey(node)) {
            // if this is a pattern input, we also need to schedule the pattern output
            for (ValueNode pOut : patternInputs.get(node)) {
                if (!scheduled.contains(pOut)) {
                    schedule(pOut);
                }
            }
        }
        if (!newlyScheduled) {
            // if the given node was already scheduled, do nothing
            return;
        }

        long prio = node instanceof InferredFactNode<?> fact
                        ? prios[fact.getGuard().getId()]
                        : prios[node.getId()];
        prio *= 2;

        queue.add(new PriorityElement(node, prio));
    }

    @Override
    public void unschedule(ArrayList<ValueNode> toUnschedule) {
        if (toUnschedule.isEmpty()) {
            return;
        }
        queue.removeIf(toUnschedule::contains);
    }

    @Override
    public void rescheduleLoopBegin(LoopBeginNode begin, boolean optimistic) {
        if (scheduled.add(begin)) {
            if (optimistic) {
                optimisticLoopBegins.add(begin);
            }
            /*
             * For rescheduling a LoopBegin, we use the base priority class of its deepest end to
             * ensure the entire loop is processed before reevaluating the LoopBegin. Additionally,
             * for priority calculation for a LoopBegin to be reevaluated, the RESCHEDULE class is
             * used.
             */

            int deepest = 0;
            for (var end : begin.loopEnds()) {
                deepest = Math.max(deepest, prios[end.getId()]);
            }

            long prio = (long) deepest * 2 + 1;
            queue.add(new PriorityElement(begin, prio));
        }
    }

    @Override
    public boolean isOptimisticLoopPhi(ValueNode value) {
        return value instanceof ValuePhiNode phi && optimisticLoopBegins.contains(phi.merge());
    }

    private record PriorityElement(ValueNode node, long priority) {
    }
}
