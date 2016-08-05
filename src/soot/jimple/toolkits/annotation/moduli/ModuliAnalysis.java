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

import soot.*;

import java.util.*;

import soot.JastAddJ.MulExpr;
import soot.jimple.*;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.*;
import soot.options.*;
//import static soot.jimple.toolkits.annotation.parity.ModuliAnalysis.Parity.*;

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
public class ModuliAnalysis extends ForwardFlowAnalysis<Unit,Map<Value, Moduli>> {
	
	public enum VALUE_TYPE {
		TOP ,
		NUMBER,
		BOTTOM ;
	}
	
	static private final int main_base = 3; 

	
    private UnitGraph g;

    private LiveLocals filter;
    
    public ModuliAnalysis(UnitGraph g, LiveLocals filter)
    {
        super(g);
        this.g = g;

        this.filter = filter;
        
        filterUnitToBeforeFlow = new HashMap<Unit, Map<Value, Moduli>>();
        buildBeforeFilterMap();
        
        filterUnitToAfterFlow = new HashMap<Unit, Map<Value, Moduli>>();
        
        doAnalysis();
        
    }

    public ModuliAnalysis(UnitGraph g){
        super(g);
        this.g = g;

        doAnalysis();
    }
    
    private void buildBeforeFilterMap(){
        
        for (Unit s : g.getBody().getUnits()) {
            //if (!(s instanceof DefinitionStmt)) continue;
            //Value left = ((DefinitionStmt)s).getLeftOp();
            //if (!(left instanceof Local)) continue;
        
            //if (!((left.getType() instanceof IntegerType) || (left.getType() instanceof LongType))) continue;

            Map<Value, Moduli> map = new HashMap<Value, Moduli>();            
            for (Local l : filter.getLiveLocalsBefore(s)) {
            	map.put(l, new Moduli(VALUE_TYPE.BOTTOM,main_base));
            }
                        
            filterUnitToBeforeFlow.put(s, map);
        } 
        //System.out.println("init filtBeforeMap: "+filterUnitToBeforeFlow);           
    }

// STEP 4: Is the merge operator union or intersection?
// 
// merge  | bottom | even   | odd   | top
// -------+--------+--------+-------+--------
// bottom | bottom | even   | odd   | top
// -------+--------+--------+-------+--------
// even   | even   | even   | top   | top
// -------+--------+--------+-------+--------
// odd    | odd    | top    | odd   | top  
// -------+--------+--------+-------+--------
// top    | top    | top    | top   | top
//

    @Override
    protected void merge(Map<Value, Moduli> inMap1, Map<Value, Moduli> inMap2, Map<Value, Moduli> outMap)
    { //new Moduli(VALUE_TYPE.BOTTOM)
	for (Value var1 : inMap1.keySet()) {
        //System.out.println(var1);
		Moduli inVal1 = inMap1.get(var1);
        //System.out.println(inVal1);
		Moduli inVal2 = inMap2.get(var1);
        //System.out.println(inVal2);
       // System.out.println("before out "+outMap.get(var1));

        if (inVal2 == null){
            outMap.put(var1, inVal1);
        }
	    else if (inVal1.equals(new Moduli(VALUE_TYPE.BOTTOM,main_base))) {
			outMap.put(var1, inVal2);
		}
		else if (inVal2.getType().equals(VALUE_TYPE.BOTTOM)) {
		        outMap.put(var1, inVal1);
		}
		else if ((inVal1.getType().equals(VALUE_TYPE.NUMBER)) &&
		   	(inVal2.getType().equals(VALUE_TYPE.NUMBER)) 
		   	&& inVal2.getBase() == inVal1.getBase() &&
			inVal1.getValue() == inVal2.getValue()){
				outMap.put(var1, new Moduli(inVal1.getValue(), inVal1.getBase()));
		}
		else {
			outMap.put(var1, new Moduli(VALUE_TYPE.TOP,main_base));
		}
	}
	
    }

// STEP 5: Define flow equations.
// in(s) = ( out(s) minus defs(s) ) union uses(s)
//

    @Override
    protected void copy(Map<Value, Moduli> sourceIn, Map<Value, Moduli> destOut) {
        destOut.clear();
        destOut.putAll(sourceIn);
    }
   
    // Parity Tests: 	even + even = even
    // 			even + odd = odd 
    // 			odd + odd = even
    //
    // 			even * even = even
    // 			even * odd = even
    // 			odd * odd = odd
    //
    // 			constants are tested mod 2
    //

    private Moduli getModuli(Map<Value, Moduli> in, Value val, int base) {
        //System.out.println("get Parity in: "+in);
        if ((val instanceof AddExpr) | (val instanceof SubExpr)) {
        	Moduli resVal1 = getModuli(in, ((BinopExpr)val).getOp1(), base);
        	Moduli resVal2 = getModuli(in, ((BinopExpr)val).getOp2(), base);
        	
	        if (resVal1.getType().equals(VALUE_TYPE.TOP) | resVal2.getType().equals(VALUE_TYPE.TOP)) {
                return new Moduli(VALUE_TYPE.TOP,main_base);
	        }  
            if (resVal1.equals(VALUE_TYPE.BOTTOM) | resVal2.equals(VALUE_TYPE.BOTTOM)){
                return new Moduli(VALUE_TYPE.BOTTOM,main_base); //TODO what should this return
            }
            
            if ((resVal1.getBase() != resVal2.getBase())){
            	return new Moduli(VALUE_TYPE.TOP,main_base); //TODO what should this return
            }
            
            if (val instanceof AddExpr){ 
            	return new Moduli(resVal1.getValue() + resVal2.getValue(),  resVal1.getBase());
            }
            else{
            	return new Moduli(resVal1.getValue() - resVal2.getValue(),  resVal1.getBase());
            }
        }
        
        
        if (val instanceof MulExpr) {
        
        	Moduli resVal1 = getModuli(in, ((BinopExpr)val).getOp1(), base);
        	Moduli resVal2 = getModuli(in, ((BinopExpr)val).getOp2(), base);
        	
	        if (resVal1.getType().equals(VALUE_TYPE.TOP) | resVal2.getType().equals(VALUE_TYPE.TOP)) {
                return new Moduli(VALUE_TYPE.TOP,main_base);
	        }  
            if (resVal1.equals(VALUE_TYPE.BOTTOM) | resVal2.equals(VALUE_TYPE.BOTTOM)){
                return new Moduli(VALUE_TYPE.BOTTOM,main_base); 
            }
            if ((resVal1.getBase() != resVal2.getBase())){
            	return new Moduli(VALUE_TYPE.TOP,main_base); 
            }
        	return new Moduli(resVal1.getValue() * resVal2.getValue(), resVal1.getBase());
        }
        
        if (val instanceof IntConstant) {
	        int value = ((IntConstant)val).value;
	        return new Moduli(value, base);
        }
        if (val instanceof LongConstant) {
	        long value = ((LongConstant)val).value;
	        return new Moduli(value, base);
        }
        
        Moduli p = in.get(val); 
        if (p == null){
        	System.err.println("ohh ohh did not expect to be here");
        	return null;//new Moduli(VALUE_TYPE.TOP,main_base);
        }
        return p;
    }
    
    @Override
    protected void flowThrough(Map<Value, Moduli> in, Unit s,
    		Map<Value, Moduli> out)
    {

	    // copy in to out 
	    out.putAll(in);
	
        // for each stmt where leftOp is defintionStmt find the parity
	    // of rightOp and update parity to EVEN, ODD or TOP

        //boolean useS = false;
        
	    if (s instanceof DefinitionStmt) {
	        Value left = ((DefinitionStmt)s).getLeftOp();
	        if (left instanceof Local) {
                if ((left.getType() instanceof IntegerType) || (left.getType() instanceof LongType)){
                    //useS = true;
	  	            Value right = ((DefinitionStmt)s).getRightOp();
		            out.put(left, getModuli(out, right,main_base));
                }
	        }
	    }

        // get all use and def boxes of s 
        // if use or def is int or long constant add their parity
        for (ValueBox next : s.getUseAndDefBoxes()) {
            Value val = next.getValue();
            //System.out.println("val: "+val.getClass());
            if (val instanceof ArithmeticConstant){
                out.put(val, getModuli(out, val,main_base));
                //System.out.println("out map: "+out);
            }
        }
        
        //if (useS){
        if (Options.v().interactive_mode()){
            buildAfterFilterMap(s);
            updateAfterFilterMap(s);
        }
        //}
    }
    
    private void buildAfterFilterMap(Unit s){
        
        Map<Value, Moduli> map = new HashMap<Value, Moduli>();
        for (Local local :  filter.getLiveLocalsAfter(s)) {
            map.put(local, new Moduli(VALUE_TYPE.BOTTOM,main_base));
        }
        filterUnitToAfterFlow.put(s, map);
        //System.out.println("built afterflow filter map: "+filterUnitToAfterFlow);
    }


// STEP 6: Determine value for start/end node, and
// initial approximation.
//
// start node: locals with BOTTOM
// initial approximation: locals with BOTTOM
    @Override
    protected Map<Value, Moduli> entryInitialFlow()
    {
	/*HashMap initMap = new HashMap();
	
	Chain locals = g.getBody().getLocals();
	Iterator it = locals.iterator();
	while (it.hasNext()) {
	  initMap.put(it.next(), BOTTOM);
	}
        return initMap;*/

        return newInitialFlow();
    }

    private void updateBeforeFilterMap() {    
        for (Unit s : filterUnitToBeforeFlow.keySet()) {
            Map<Value, Moduli> allData = getFlowBefore(s);            
            Map<Value, Moduli> filterData = filterUnitToBeforeFlow.get(s);
            filterUnitToBeforeFlow.put(s, updateFilter(allData, filterData));            
        }
    }
        
    private void updateAfterFilterMap(Unit s) {    
    	Map<Value, Moduli> allData = getFlowAfter(s);            
    	Map<Value, Moduli> filterData = filterUnitToAfterFlow.get(s);
        filterUnitToAfterFlow.put(s, updateFilter(allData, filterData));            
    }
        
    private Map<Value, Moduli> updateFilter(Map<Value, Moduli> allData, Map<Value, Moduli> filterData){

        if (allData == null) 
        	return filterData;

        for (Value v : filterData.keySet()) {
        	Moduli d = allData.get(v);
            if (d == null) {
            	filterData.remove(v);
            } else {
                filterData.put(v, d);
            }
        }

        return filterData;
    }
    
    @Override
    protected Map<Value, Moduli> newInitialFlow()
    {
	    Map<Value, Moduli> initMap = new HashMap<Value, Moduli>();
	
	    for (Local l : g.getBody().getLocals()) {
	    	Type t = l.getType();
            //System.out.println("next local: "+next);
            if ((t instanceof IntegerType) || (t instanceof LongType)) {
	            initMap.put(l, new Moduli(VALUE_TYPE.BOTTOM,main_base));
            }
	    }
    
        for (ValueBox vb : g.getBody().getUseAndDefBoxes()) {
            Value val = vb.getValue();
            if (val instanceof ArithmeticConstant) {
                initMap.put(val, getModuli(initMap, val,main_base));
            }
        }

        if (Options.v().interactive_mode()){
            updateBeforeFilterMap();
        }
        
        return initMap;

    }
        

}
