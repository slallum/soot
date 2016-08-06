/* Soot - a J*va Optimization Framework
 * Copyright (C) 2003 Jennifer Lhotak
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

package soot.jimple.toolkits.annotation.moduli;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import soot.IntegerType;
import soot.Local;
import soot.LongType;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.JastAddJ.MulExpr;
import soot.jimple.AddExpr;
import soot.jimple.ArithmeticConstant;
import soot.jimple.BinopExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.IntConstant;
import soot.jimple.LongConstant;
import soot.jimple.SubExpr;
import soot.jimple.internal.JMulExpr;
//import static soot.jimple.toolkits.annotation.parity.ModuliAnalysis.Parity.*;
import soot.options.Options;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;
import soot.toolkits.scalar.LiveLocals;

// STEP 1: What are we computing?
// SETS OF PAIRS of form (X, T) => Use ArraySparseSet.
//
// STEP 2: Precisely define what we are computing.
// For each statement compute the parity of all variables 
// in the program.
// 
// STEP 3: Decide whether it is a backwards or forwards analysis.
// FORWARDS
//
//
public class PreciseModuliAnalysis
		extends
		ForwardFlowAnalysis<Unit, Map<Value, PreciseModuliAnalysis.PreciseModuli>> {

	public class PreciseModuli {

		private ArrayList<Moduli> abstractValues = new ArrayList<Moduli>();

		public PreciseModuli(ModuliAnalysis.VALUE_TYPE type, int base) {
			if (type == ModuliAnalysis.VALUE_TYPE.NUMBER){
				throw new IllegalStateException ("moduli of type number must be created with a concerete value number");
			}
			for (int i = 2; i <= base; i++) {
				if (type == ModuliAnalysis.VALUE_TYPE.BOTTOM) {
					abstractValues.add(new Moduli(ModuliAnalysis.VALUE_TYPE.BOTTOM, i));
				} else {
					abstractValues.add(new Moduli(
							ModuliAnalysis.VALUE_TYPE.TOP, i));
				}
			}
		}

		public PreciseModuli(ArrayList<Moduli> abstractValues) {
			this.abstractValues = abstractValues;
		}

		public PreciseModuli(int val, int base) {
			for (int i = 2; i <= base; i++) {
				abstractValues.add(new Moduli(val, i));
			}
		}

		public PreciseModuli(long val, int base) {
			for (int i = 2; i <= base; i++) {
				abstractValues.add(new Moduli(val, i));
			}
		}

		ArrayList<Moduli> getValue() {
			return abstractValues;
		}

		public boolean equalsName(String otherName) {
			if (otherName == null)
				return false;
			return String.valueOf(this.toString()).equals(otherName.toString());
		}

		@Override
		public String toString() {

			String r = "<";
			for (Moduli m : abstractValues) {
				r += m.toString() + ",";
			}
			r = r.substring(0, r.length() - 1) + ">";
			return r;
		}

		@Override
		public boolean equals(Object otherName) {
			if (otherName == null)
				return false;
			return String.valueOf(this.toString()).equals(otherName.toString());
		}
		
		@Override
		public int hashCode() {
			return this.toString().hashCode();
		}
		
	}

	private UnitGraph g;

	private LiveLocals filter;

	public PreciseModuliAnalysis(UnitGraph g, LiveLocals filter,
			int max_moduli_range) {
		super(g);
		this.g = g;

		this.main_base = max_moduli_range;
		this.filter = filter;

		filterUnitToBeforeFlow = new HashMap<Unit, Map<Value, PreciseModuli>>();
		buildBeforeFilterMap();

		filterUnitToAfterFlow = new HashMap<Unit, Map<Value, PreciseModuli>>();

		doAnalysis();

	}

	private int main_base = 5;

	public PreciseModuliAnalysis(UnitGraph g, int max_moduli_range) {
		super(g);
		this.g = g;
		this.main_base = max_moduli_range;

		doAnalysis();
	}

	private void buildBeforeFilterMap() {

		for (Unit s : g.getBody().getUnits()) {

			Map<Value, PreciseModuli> map = new HashMap<Value, PreciseModuli>();
			for (Local l : filter.getLiveLocalsBefore(s)) {
				map.put(l, new PreciseModuli(ModuliAnalysis.VALUE_TYPE.BOTTOM,
						main_base));
			}

			filterUnitToBeforeFlow.put(s, map);
		}
		// System.out.println("init filtBeforeMap: "+filterUnitToBeforeFlow);
	}

	// STEP 4: Is the merge operator union
	
	@Override
	protected void merge(Map<Value, PreciseModuli> inMap1,
			Map<Value, PreciseModuli> inMap2, Map<Value, PreciseModuli> outMap) { // new
																					// Moduli(VALUE_TYPE.BOTTOM)
		for (Value var1 : inMap1.keySet()) {
			// System.out.println(var1);
			PreciseModuli inVal1 = inMap1.get(var1);
			// System.out.println(inVal1);
			PreciseModuli inVal2 = inMap2.get(var1);
			// System.out.println(inVal2);
			// System.out.println("before out "+outMap.get(var1));

			if (inVal2 == null) {
				outMap.put(var1, inVal1);
				return;
			}
			if (inVal1 == null) {
				outMap.put(var1, inVal2);
				return;
			}

			ArrayList<Moduli> abstractValues_1 = inVal1.getValue();
			ArrayList<Moduli> abstractValues_2 = inVal2.getValue();
			ArrayList<Moduli> abstractValues_res = new ArrayList<Moduli>();

			if (abstractValues_1 == null || abstractValues_2 == null){
				throw new IllegalStateException ("abstract values array is expected to be non null");
			}

//			System.out.println("********************************************");
//			System.out.println(abstractValues_1);
//			System.out.println(abstractValues_2);

			for (int i = 0; i < abstractValues_1.size(); i++) {

				Moduli i_val_1 = abstractValues_1.get(i);
				Moduli i_val_2 = abstractValues_2.get(i);
				ModuliAnalysis.VALUE_TYPE t1 = i_val_1.getType();
				ModuliAnalysis.VALUE_TYPE t2 = i_val_2.getType();

				if (t1 == (ModuliAnalysis.VALUE_TYPE.BOTTOM)) {
//					System.out.println(i_val_1 + "," + i_val_2 + ":" + new Moduli(i_val_2).getType());
					abstractValues_res.add(new Moduli(i_val_2));
					continue;
				}

				if (t2 == (ModuliAnalysis.VALUE_TYPE.BOTTOM)) {
//					System.out.println(i_val_1 + "," + i_val_2 + ":" + new Moduli(i_val_1).getType());
					abstractValues_res.add(new Moduli(i_val_1));
					continue;
				}

				if (t1 == (ModuliAnalysis.VALUE_TYPE.TOP)
						|| t2 == (ModuliAnalysis.VALUE_TYPE.TOP)) {
					abstractValues_res.add(new Moduli(
							ModuliAnalysis.VALUE_TYPE.TOP, i+2));
//					System.out.println(i_val_1 + "," + i_val_2 + ":" + 
							new Moduli(ModuliAnalysis.VALUE_TYPE.TOP, i+2).getType();
					continue;
				}

				// Ensuring correct location of elements (i.e., order moduli bases as the Natural numbers) :
				if (i_val_1.getBase() != (i + 2)
						|| i_val_2.getBase() != (i + 2)) {
					throw new IllegalStateException(
							"abstract values in the wrong location of abstract values array "
									+ ", expected " + i + ", but in "
									+ (i_val_1.getBase() - 2) + " and "
									+ (i_val_2.getBase() - 2) + " - "
									+ i_val_1.getValue() + " and "
									+ i_val_2.getValue()
									+ "-" + t1 + " and "
									+ t2);
				}
				
				// If we have two numbers:
				if (i_val_1.getValue() == i_val_2.getValue()
						&& i_val_1.getBase() == i_val_2.getBase()) {
					abstractValues_res.add(new Moduli(i_val_1.getValue(), i+2));
				} else {
					abstractValues_res.add(new Moduli(
							ModuliAnalysis.VALUE_TYPE.TOP, i+2));
				}
			}
			if (!(abstractValues_res.size() != main_base)){
				throw new IllegalStateException ("abstract values array is smaller than the expected max_size=" + main_base);
			}
			if (abstractValues_res.size() != abstractValues_2.size()){
				throw new IllegalStateException("merge went wrong!");
			}
//			System.out.println(abstractValues_res);
//			System.out.println("********************************************");
			outMap.put(var1, new PreciseModuli(abstractValues_res));
		}

	}

	// STEP 5: Define flow equations.
	// in(s) = ( out(s) minus defs(s) ) union uses(s)
	//

	@Override
	protected void copy(Map<Value, PreciseModuli> sourceIn,
			Map<Value, PreciseModuli> destOut) {
		destOut.clear();
		destOut.putAll(sourceIn);
	}

	private PreciseModuli getModuli(Map<Value, PreciseModuli> in, Value val) {
		// System.out.println("get Parity in: "+in);

		if ((val instanceof AddExpr) | (val instanceof SubExpr)
				| (val instanceof MulExpr) | (val instanceof JMulExpr)) {

			PreciseModuli resVal1 = getModuli(in, ((BinopExpr) val).getOp1());
			PreciseModuli resVal2 = getModuli(in, ((BinopExpr) val).getOp2());

			ArrayList<Moduli> abstractValues_1 = resVal1.getValue();
			ArrayList<Moduli> abstractValues_2 = resVal2.getValue();
			ArrayList<Moduli> abstractValues_res = new ArrayList<Moduli>();

			
			if (abstractValues_1 == null || abstractValues_2 == null){
				throw new IllegalStateException ("abstract values array is expected to be non null");
			}

			for (int i = 0; i < abstractValues_1.size(); i++) {

				Moduli i_val_1 = abstractValues_1.get(i);
				Moduli i_val_2 = abstractValues_2.get(i);
				ModuliAnalysis.VALUE_TYPE t1 = i_val_1.getType();
				ModuliAnalysis.VALUE_TYPE t2 = i_val_2.getType();

				if (t1.equals(ModuliAnalysis.VALUE_TYPE.TOP)
						|| t2.equals(ModuliAnalysis.VALUE_TYPE.TOP)) {
					abstractValues_res.add(new Moduli(
							ModuliAnalysis.VALUE_TYPE.TOP, i));
					continue;
				}
				if (t1.equals(ModuliAnalysis.VALUE_TYPE.BOTTOM)
						&& t2.equals(ModuliAnalysis.VALUE_TYPE.BOTTOM)) {
					abstractValues_res.add(new Moduli(
							ModuliAnalysis.VALUE_TYPE.BOTTOM, i));
					continue;
				}
				int base = i_val_1.getBase();
				if (i_val_1.getBase() != i_val_2.getBase()){
					throw new IllegalStateException ("cannot add values of different modulu base");
				}
				int res = 0;
				if (val instanceof AddExpr) {
					res = i_val_1.getValue() + i_val_2.getValue();
				}
				if (val instanceof SubExpr) {
					res = i_val_1.getValue() - i_val_2.getValue();
				}
				if (val instanceof MulExpr | val instanceof JMulExpr) {
					res = i_val_1.getValue() * i_val_2.getValue();
				}
				abstractValues_res.add(new Moduli(res, base));

			}
			return new PreciseModuli(abstractValues_res);
		}

		if (val instanceof IntConstant) {
			int value = ((IntConstant) val).value;
			return new PreciseModuli(value, main_base);
		}
		if (val instanceof LongConstant) {
			long value = ((LongConstant) val).value;
			return new PreciseModuli(value, main_base);
		}

		PreciseModuli p = in.get(val);
		if (p == null)
			return new PreciseModuli(ModuliAnalysis.VALUE_TYPE.TOP, main_base); 
		return p;
	}

	@Override
	protected void flowThrough(Map<Value, PreciseModuli> in, Unit s,
			Map<Value, PreciseModuli> out) {

		// copy in to out
		out.putAll(in);

		// for each stmt where leftOp is defintionStmt find the moduli
		// of rightOp and update accordingly 

		// boolean useS = false;

		if (s instanceof DefinitionStmt) {
			Value left = ((DefinitionStmt) s).getLeftOp();
			
			if (left instanceof Local) {
				if ((left.getType() instanceof IntegerType)
						|| (left.getType() instanceof LongType)) {
					// useS = true;
					Value right = ((DefinitionStmt) s).getRightOp();
					out.put(left, getModuli(out, right));
				}
			}
		}

		// get all use and def boxes of s
		// if use or def is int or long constant add their moduli
		for (ValueBox next : s.getUseAndDefBoxes()) {
			Value val = next.getValue();
			// System.out.println("val: "+val.getClass());
			if (val instanceof ArithmeticConstant) {
				out.put(val, getModuli(out, val));
				// System.out.println("out map: "+out);
			}
		}

		// if (useS){
		if (Options.v().interactive_mode()) {
			buildAfterFilterMap(s);
			updateAfterFilterMap(s);
		}
		// }
	}

	private void buildAfterFilterMap(Unit s) {

		Map<Value, PreciseModuli> map = new HashMap<Value, PreciseModuli>();
		for (Local local : filter.getLiveLocalsAfter(s)) {
			map.put(local, new PreciseModuli(ModuliAnalysis.VALUE_TYPE.BOTTOM,
					main_base));
		}
		filterUnitToAfterFlow.put(s, map);
	}

	// STEP 6: Determine value for start/end node, and
	// initial approximation.
	//
	// start node: locals with BOTTOM
	// initial approximation: locals with BOTTOM
	@Override
	protected Map<Value, PreciseModuli> entryInitialFlow() {
		/*
		 * HashMap initMap = new HashMap();
		 * 
		 * Chain locals = g.getBody().getLocals(); Iterator it =
		 * locals.iterator(); while (it.hasNext()) { initMap.put(it.next(),
		 * BOTTOM); } return initMap;
		 */

		return newInitialFlow();
	}

	private void updateBeforeFilterMap() {
		for (Unit s : filterUnitToBeforeFlow.keySet()) {
			Map<Value, PreciseModuli> allData = getFlowBefore(s);
			Map<Value, PreciseModuli> filterData = filterUnitToBeforeFlow
					.get(s);
			filterUnitToBeforeFlow.put(s, updateFilter(allData, filterData));
		}
	}

	private void updateAfterFilterMap(Unit s) {
		Map<Value, PreciseModuli> allData = getFlowAfter(s);
		Map<Value, PreciseModuli> filterData = filterUnitToAfterFlow.get(s);
		filterUnitToAfterFlow.put(s, updateFilter(allData, filterData));
	}

	private Map<Value, PreciseModuli> updateFilter(
			Map<Value, PreciseModuli> allData,
			Map<Value, PreciseModuli> filterData) {

		if (allData == null)
			return filterData;

		for (Value v : filterData.keySet()) {
			PreciseModuli d = allData.get(v);
			if (d == null) {
				filterData.remove(v);
			} else {
				filterData.put(v, d);
			}
		}
		return filterData;
	}

	@Override
	protected Map<Value, PreciseModuli> newInitialFlow() {
		Map<Value, PreciseModuli> initMap = new HashMap<Value, PreciseModuli>();

		for (Local l : g.getBody().getLocals()) {
			Type t = l.getType();
			// System.out.println("next local: "+next);
			if ((t instanceof IntegerType) || (t instanceof LongType)) {
				initMap.put(l, new PreciseModuli(
						ModuliAnalysis.VALUE_TYPE.BOTTOM, main_base));
			}
		}

		for (ValueBox vb : g.getBody().getUseAndDefBoxes()) {
			Value val = vb.getValue();
			if (val instanceof ArithmeticConstant) {
				initMap.put(val, getModuli(initMap, val));
			}
		}

		if (Options.v().interactive_mode()) {
			updateBeforeFilterMap();
		}

		return initMap;

	}
	
	void assertTrue (boolean b, String msg){
		if (b) return; 
		System.err.println("Unexpected states: " + msg);
		System.exit(0);
	}

}
