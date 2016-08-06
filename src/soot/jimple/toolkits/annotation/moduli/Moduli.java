package soot.jimple.toolkits.annotation.moduli;

import soot.jimple.toolkits.annotation.moduli.ModuliAnalysis.VALUE_TYPE;

public class Moduli {

	private int base;   
	private int value = 0;   
	private VALUE_TYPE type;

	
	public Moduli(int s, int base) {
		this.base = base;
		value = s % base;
		type = VALUE_TYPE.NUMBER;
	}
	
	public Moduli(long s, int base) {
		this.base = base;
		value = (int)(s % base); 
		type = VALUE_TYPE.NUMBER;
	}

	public Moduli(VALUE_TYPE type, int base) {
		assert(type != VALUE_TYPE.NUMBER);
		this.base = base;
		this.type = type; 
	}
	
	public Moduli(Moduli m) {
		this.base = m.base;
		value = m.value;
		type = m.type;
	}
	
	int getValue () {
		assert(type == VALUE_TYPE.NUMBER);
		return value;
	}

	
	VALUE_TYPE getType () {
		return type;
	}
	
	int getBase() {
		return base;
	}
	
    public boolean equalsName(String otherName) {
        if (otherName == null) return false;
        return String.valueOf(this.value).equals(otherName.toString());
    }
    
    @Override
    public String toString() {
    	if (type == VALUE_TYPE.BOTTOM){
    		return "buttom";
    	}
    	if (type == VALUE_TYPE.TOP){
    		return "top";
    	}
       return String.valueOf(this.value);
    }
    
	@Override
	public int hashCode() {
		return this.toString().hashCode();
	}
	
}
