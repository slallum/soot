package soot.jimple.toolkits.annotation.moduli;

import soot.*;

import java.util.*;

import soot.toolkits.graph.*;
import soot.toolkits.scalar.*;
import soot.tagkit.*;
import soot.jimple.*;
import soot.options.*;


public class PreciseModuliTagger extends BodyTransformer {

	
	private int max_moduli_range = 5;
	public PreciseModuliTagger( Singletons.Global g , int max_moduli_range) {this.max_moduli_range = max_moduli_range;}
    public static PreciseModuliTagger v() { return G.v().instance_soot_jimple_toolkits_annotation_PreciseModuliTagger(); }

    protected void internalTransform(
            Body b, String phaseName, Map options)
    {

//        System.out.println("modulu tagger for method: " ); //+ b.getMethod().getName()
        boolean isInteractive = Options.v().interactive_mode();
        Options.v().set_interactive_mode(false);
        PreciseModuliAnalysis a;
        
        if (isInteractive){
            LiveLocals sll = new SimpleLiveLocals(new BriefUnitGraph(b));
            Options.v().set_interactive_mode(isInteractive);
        
            a = new PreciseModuliAnalysis(
		        new BriefUnitGraph( b ) , sll, max_moduli_range);
        }
        else {
            a = new PreciseModuliAnalysis(new BriefUnitGraph(b), max_moduli_range);
        }
        
        Iterator sIt = b.getUnits().iterator();
        while( sIt.hasNext() ) {

            Stmt s = (Stmt) sIt.next();
            HashMap moduliVars = (HashMap) a.getFlowAfter( s );

            Iterator it = moduliVars.keySet().iterator();
            while( it.hasNext() ) {
			
                final Value variable = (Value) it.next();
                if ((variable instanceof IntConstant) || (variable instanceof LongConstant)){
                    // don't add string tags (just color tags)
                }
                else{
                    StringTag t = new StringTag(
                        "Moduli variable: "+variable+" "+
                        moduliVars.get(variable) , "Moduli Analysis");
                    s.addTag( t );
                }
            }

			HashMap moduliVarsUses = (HashMap) a.getFlowBefore( s );
			HashMap moduliVarsDefs = (HashMap) a.getFlowAfter( s );

			
			//uses
			System.out.println("analyzing line: " + s.getJavaSourceStartLineNumber());
			Iterator valBoxIt = s.getUseBoxes().iterator();
			
			int size = 0;
			while (valBoxIt.hasNext()){
				size++;
				ValueBox vb = (ValueBox)valBoxIt.next();
				if (moduliVarsUses.containsKey(vb.getValue())){
					Object o = moduliVarsUses.get(vb.getValue());
					String type = o.toString();
					G.v().out.println(vb.getValue() + ": " + type );
					addColorTag(vb, type);
				}
			}

			// defs

			valBoxIt = s.getDefBoxes().iterator();
			
			while (valBoxIt.hasNext()){
				ValueBox vb = (ValueBox)valBoxIt.next();
				if (moduliVarsDefs.containsKey(vb.getValue())){
					Object o =  moduliVarsDefs.get(vb.getValue());
					String type = o.toString();
					G.v().out.println(vb.getValue() + ": " + type );
					addColorTag(vb, type);
				}
			}
        }

        // add key to class
        Iterator keyIt = b.getMethod().getDeclaringClass().getTags().iterator();
        boolean keysAdded = false;
        while (keyIt.hasNext()){
            Object next = keyIt.next();
            if (next instanceof KeyTag){
                if (((KeyTag)next).analysisType().equals("Moduli Analysis")){
                    keysAdded = true;
                }
            }
        }
        if (!keysAdded){
            b.getMethod().getDeclaringClass().addTag(new KeyTag(255,0,0, "Moduli: Top", "Parity Analysis"));
            b.getMethod().getDeclaringClass().addTag(new KeyTag(255,248,35, "Moduli: Bottom", "Parity Analysis"));
            b.getMethod().getDeclaringClass().addTag(new KeyTag(174,210,255, "Moduli: Number", "Parity Analysis"));
        }
    }

	private void addColorTag(ValueBox vb, String type) {
		if (type.equals("bottom")){
			//green
			vb.addTag(new ColorTag(ColorTag.GREEN, "Moduli Analysis"));
		}
		else if (type.equals("top")){
			//red
			vb.addTag(new ColorTag(ColorTag.RED, "Moduli Analysis"));
		}
		else {
			//blue
			vb.addTag(new ColorTag(ColorTag.BLUE, "Moduli Analysis"));
		}
		
	}

	
}
