package edu.wis.jtlv.lib.mc.RTCTLK;

import edu.wis.jtlv.env.Env;
import edu.wis.jtlv.env.core.smv.schema.SMVAgentInfo;
import edu.wis.jtlv.env.module.Module;
import edu.wis.jtlv.env.module.ModuleWithStrongFairness;
import edu.wis.jtlv.env.spec.*;
import edu.wis.jtlv.lib.AlgExceptionI;
import edu.wis.jtlv.lib.AlgResultI;
import edu.wis.jtlv.lib.AlgResultPath;
import edu.wis.jtlv.lib.AlgResultString;
import edu.wis.jtlv.lib.mc.CTL.CTLModelCheckAlg;
import edu.wis.jtlv.lib.mc.ModelCheckAlgException;
import edu.wis.jtlv.old_lib.mc.ModelCheckException;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDVarSet;

import static edu.wis.jtlv.env.spec.Operator.*;

public class RTCTLKModelCheckAlg extends CTLModelCheckAlg{
    public RTCTLKModelCheckAlg(ModuleWithStrongFairness design, Spec property) {
        super(design, property);
    }
    //add
    Module design = getDesign();
    BDD feas = design.feasible();//所有的可达状态
    // agentName KNOW p
    // forall(system_global_variables - agentName's visible_variables).((global_reachable_states & fair_states) -> p)
    public BDD know(String agentName, BDD p) throws ModelCheckAlgException {
        if(agentName.equals("")) throw new ModelCheckAlgException("The agent name of the knowledge formula is null.");

        int idx_dot = agentName.indexOf('.');
        if(idx_dot==-1)
            agentName = "main." + agentName;
        else if (!agentName.substring(0, idx_dot).equals("main."))
            throw new ModelCheckAlgException("The agent's name " + agentName + " is illegal.");

        SMVAgentInfo agentInfo = Env.getAll_agent_modules().get(agentName);
        if(agentInfo==null) throw new ModelCheckAlgException("Cannot find the information of agent " + agentName + ".");

        BDDVarSet visVars = agentInfo.getVisVars_BDDVarSet();
        // X - agentName's visible variables
        BDDVarSet allInvisVars = Env.globalUnprimeVarsMinus(visVars);

        BDD FairReachStates = getFairStates().and(getReachableStates());

        BDD res = FairReachStates.imp(p).forAll(allInvisVars);

        return res;
    }

    public BDD satRTCTLK(Spec property) throws ModelCheckAlgException {
        if (property instanceof SpecBDD)
            return ((SpecBDD) property).getVal();
        // else it is SpecExp since this cannot be a Real Time CTL.
        // and it also cannot be a triplet operator.
        SpecExp propExp = (SpecExp) property;
        Operator op = propExp.getOperator();
        Spec[] child = propExp.getChildren();

        //Uppdate by LS on : 2017/10/21
        int noo = op.numOfOperands();
        SpecRange range = null;
        BDD left=null; BDD right=null;

        if (noo==1) //EX, EF, EG, AX, AF,AG left
            left=satRTCTLK(child[0]);
        if (noo==2) {//ABF, ABG, EBF, EBG  left or right//区间不作节点
            if (child[0] instanceof SpecRange)
            {   range = (SpecRange) child[0];
                left= satRTCTLK(child[1]); }
            else if(op == Operator.KNOW) {
                left = null;
                right = satRTCTLK(child[1]);
            }
            else
            {   left=satRTCTLK(child[0]);//AU GU
                right=satRTCTLK(child[1]);
            }
        }
        if (noo==3)// ABU, EBU
        {
            if (child[1] instanceof SpecRange) {
                range = (SpecRange) child[1];
                left = satRTCTLK(child[0]);
                right = satRTCTLK(child[2]);
            }
        }
        // propositional
        if (op == Operator.NOT)
            return left.not();
        if (op == Operator.AND)
            return left.and(right);
        if (op == Operator.OR)
            return left.or(right);
        if (op == Operator.XOR)
            return left.xor(right);
        if (op == Operator.XNOR)
            return left.xor(right).not();
        if (op == Operator.IFF)
            return left.biimp(right);
        if (op == Operator.IMPLIES)
            return left.imp(right);

        // unbounded CTL temporal
        if (op == Operator.EX)
            return EfX(left);
        if (op == Operator.AX)
            return AfX(left);
        if (op == Operator.EF)
            return EfF(left);
        if (op == Operator.AF)
            return AfF(left);
        if (op == Operator.EG)
            return EfG(left);
        if (op == Operator.AG)
            return AfG(left);
        if (op == Operator.AU)
            return AfU(left, right);
        if (op == Operator.EU)
            return EfU(left, right);

        // bounded CTL temporal
        if (op == Operator.EBU)
            return EfBU(range.getFrom(), range.getTo(), left, right);//EfBU(int from, int to, BDD p, BDD q)
        if (op == Operator.ABU)//AfBU(int from, int to, BDD p, BDD q)
            return AfBU(range.getFrom(), range.getTo(), left, right);
        if (op == Operator.EBF)//EfBF(int from, int to, BDD p)
            return EfBF(range.getFrom(), range.getTo(), left);
        if (op == Operator.ABF)//(int from, int to, BDD p)
            return AfBF(range.getFrom(), range.getTo(), left);
        if (op == Operator.EBG)//(int from, int to, BDD p)
            return EfBG(range.getFrom(), range.getTo(), left);
        if (op == Operator.ABG)//AfBG(int from, int to, BDD p)
            return AfBG(range.getFrom(), range.getTo(), left);

        // epistemic
        if (op == Operator.KNOW) {
            String agentName = child[0].toString();
            return know(agentName, right);
        }
        // something is wrong.
        throw new ModelCheckAlgException(
                "Cannot identify root operator for sub specification: " + property);
    }
    @Override
    public AlgResultI preAlgorithm() throws AlgExceptionI {
        if (!getProperty().isRealTimeCTLKSpec())
            throw new ModelCheckAlgException("Cannot model check non RTCTLK specification: " + getProperty());
        return null;
    }
    @Override
    public AlgResultI doAlgorithm() throws AlgExceptionI {
        System.out.println("model checking RTCTLK: " + getProperty());
        if (getProperty() == null)
            return new AlgResultString(false, "Cannot model check a null specification.");
        if (!getProperty().isRealTimeCTLKSpec())
            return new AlgResultString("Cannot model check non RTCTLK specification: " + getProperty());

        //setFairStates(Env.TRUE());

        // could throw an exception...
        BDD calculateStates = satRTCTLK(getProperty());
        BDD FairInitStates = getDesign().initial().and(getFairStates());
//		if (!getDesign().initial().imp(calculateStates).not().isZero()) {
        if(FairInitStates.imp(calculateStates).isOne()){
            return new AlgResultString(true, "*** Property is VALID ***");
        }else{
            BDD[] example = new BDD[0];
            try {
                example = extractWithness(getProperty());
            } catch (ModelCheckException e) {
                e.printStackTrace();
            }
            if (example==null)
                return new AlgResultString(false, "*** Property is NOT VALID ***");
            else
                return new AlgResultPath(false, example);
        }
    }

    /*
    begin RTCTLK counterexample
     */
    private BDD[] extractWithness(Spec property) throws ModelCheckException, ModelCheckAlgException {
        //System.out.println("Spec  "+property+"initial  "+property);
        SpecExp propExp = (SpecExp) property;
        Operator op = propExp.getOperator();
        if(op==EX|op==EF|op==EG|op==EU|op==EBF|op==EBG|op==EBU) return null;
        Spec[] child = propExp.getChildren();
        int noo = op.numOfOperands();
        SpecRange range = null;
        BDD left=null;
        BDD right=null;
        if (noo==1) //EX, EF, EG, AX, AF,AG left
            left=satRTCTLK(child[0]);
        if (noo==2) {//ABF, ABG, EBF, EBG  left or right
            if (child[0] instanceof SpecRange)
            { range = (SpecRange) child[0];
                left=satRTCTLK(child[1]);}//xxxxxxxx
            else
            {   left=satRTCTLK(child[0]);//AU GU
                right=satRTCTLK(child[1]);
            }
        }
        if (noo==3)// ABU, EBU
        {
            if (child[1] instanceof SpecRange)
            { range = (SpecRange) child[1];
                left=satRTCTLK(child[0]);
                right=satRTCTLK(child[2]);
            }
        }
        //设置initial()为起点
        BDD s=design.initial().and(design.feasible().satOne(design.moduleUnprimeVars(),false));
        switch (op) {
            /** Except for NOT、FINALLY、GLOBALLY、HISTORICALLY、NEXT、NOT_PREV_NOT、ONCE、PREV、B_FINALLY、B_GLOBALLY
             AND、OR、XOR、XNOR、IFF、IMPLIES、RELEASES、SINCE、TRIGGERED、UNTIL、B_UNTIL、B_UNTIL0 **/
            case AX:
                return EX_example(s, left.not());
            case AG:
                return EU_example(s,Env.TRUE(),left.not());
            case AF:
                return EG_example(s,left.not());
            case AU:
                BDD[] EU= EU_example(s,right.not(),left.not().and(right.not()));
                if (EU==null){
                    BDD[] EG= EG_example(s,right.not());
                    return EG;}
                return EU;
            case ABF:
                return EBG_example(s,range.getFrom(), range.getTo(),left.not());
            case ABG:
                return EBU_example(s,range.getFrom(), range.getTo(),Env.TRUE(),left.not());
            case ABU:
                BDD[] EBU= EBU_example(s,range.getFrom(), range.getTo(),right.not(),left.not().and(right.not()));
                if (EBU==null){
                    BDD[] EBG= EBG_example(s,range.getFrom(), range.getTo(),right.not());
                    return EBG;}
                return EBU;
//				System.out.println("EBG-----------------------------------------------------------");
//				for(int i=0;i<EBG.length  ;i++)
//				{  if(EBG[i]==null)break;
//					System.out.println(i+"---"+EBG[i]);
//				}
//				System.out.println("EBU-----------------------------------------------------------");
//				for(int i=0;i<EBU.length  ;i++)
//				{  if(EBU[i]==null)break;
//					System.out.println(i+"---"+EBU[i]);
//				}
            case KNOW:{
                 String agentName = child[0].toString();
                return KNOW_example(agentName,s,range.getFrom(), range.getTo(),left.not());
            }
        }
        return null;
    }

    public BDD[] KNOW_example(String agentName,BDD s,int from, int to, BDD f){
        BDD[] returned_path = new BDD[100];
        if (!s.and(f).equals(Env.FALSE())){
          returned_path[0]=s;
          return returned_path;}
        BDD start=getDesign().initial();

        SMVAgentInfo agentInfo = Env.getAll_agent_modules().get(agentName);
        BDDVarSet visVars = agentInfo.getVisVars_BDDVarSet();
        // X - agentName's visible variables
        BDDVarSet allInvisVars = Env.globalUnprimeVarsMinus(visVars);
        BDD FairReachStates = getFairStates().and(getReachableStates());
        BDD end = FairReachStates.imp(f).forAll(allInvisVars);
        BDD subpath[]=getDesign().shortestPath(start,end);

        return subpath;
    }

      /*
    end RTCTLK counterexample
     */
}



