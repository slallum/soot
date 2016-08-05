package soot.jimple.toolkits.annotation.moduli;

import soot.*;
import java.util.*;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.*;
import soot.tagkit.*;
import soot.jimple.*;
import soot.options.*;


public class ModuliTagger extends BodyTransformer {

	public ModuliTagger( Singletons.Global g ) {}
    public static ModuliTagger v() { return G.v().instance_soot_jimple_toolkits_annotation_moduliTagger(); }

    protected void internalTransform(
            Body b, String phaseName, Map options)
    {

        System.out.println("modulu tagger for method: " ); //+ b.getMethod().getName()
        boolean isInteractive = Options.v().interactive_mode();
        Options.v().set_interactive_mode(false);
        ModuliAnalysis a;
        
        if (isInteractive){
            LiveLocals sll = new SimpleLiveLocals(new BriefUnitGraph(b));
            Options.v().set_interactive_mode(isInteractive);
        
            a = new ModuliAnalysis(
		        new BriefUnitGraph( b ) , sll);
        }
        else {
            a = new ModuliAnalysis(new BriefUnitGraph(b));
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
			
			Iterator valBoxIt = s.getUseBoxes().iterator();
			
			while (valBoxIt.hasNext()){
				ValueBox vb = (ValueBox)valBoxIt.next();
				if (moduliVarsUses.containsKey(vb.getValue())){
					Object o = moduliVarsUses.get(vb.getValue());
					String type = o.toString();
					G.v().out.println("Moduli variable for: " + vb.getValue() + "-" + type );
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
					G.v().out.println("Moduli variable for: "+vb.getValue() + "-" + type );
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
