import YM.TraceExtension.Lamp.Aura
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {F: Peat G f}{Y:Gal G f}
abbrev Kane (F:Peat G f):= approached (Kbody F)
abbrev Tane (Y:Gal G f):= approached (Tbody Y)
-- gauge insertion purely PSUED with physical Character site. computes at finite.
lemma beat_duo {I:Type}[Fintype I][DecidableEq I] (F:Corn I→ℝ)(a b:Corn I): beat F 0 2 ![axes a,axes b]=↑(iteratedFDeriv ℝ 2 F 0 ![a,b]):=by rw [show ![axes a,axes b]=axes ∘ (![a,b]:Fin 2→_) from funext (fun i=>by fin_cases i<;>rfl)];exact beat_real ..
omit [DecidableEq I] in
lemma p_dot {x y:Corn I} : dotProduct (axes x) (axes y)=((dotProduct x y:ℝ):ℂ):=by unfold dotProduct; push_cast; rfl
lemma rill_wave (h:G.Simple)(hf:Cleric F)(hv:Cloaked Y) (p q:Phase (Lines G f 1)):
    beat (rill F Y ∘ input G f) 0 2 ![p,q]=dotProduct (Tane Y *ᵥ p) (Kane F *ᵥ q)+dotProduct (Tane Y *ᵥ q) (Kane F *ᵥ p):=by
    have ht(a b: Link G f) : beat (rill F Y ∘ input G f) 0 2 ![axes a,axes b] = dotProduct (Tane Y*ᵥ axes a) (Kane F*ᵥ axes b)+dotProduct (Tane Y*ᵥ axes b) (Kane F*ᵥ axes a):=by
        rw [beat_duo, rill_state h hf hv |>.2,Tane,Kane,prom_vec,prom_vec,prom_vec,prom_vec, p_dot,p_dot];exact Complex.ofReal_add ..
    refine Leads.two (p:=fun p q=> beat (rill F Y ∘ input G f) 0 2 ![p,q]) (q:=fun p q=> dotProduct (Tane Y*ᵥ p) (Kane F*ᵥ q)+dotProduct (Tane Y*ᵥ q) (Kane F*ᵥ p)) (fun i => left_beat _ i) (fun i=> right_beat _ i) (fun i=> ?_) (fun i=>?_) ht p q
    all_goals intro u v; simp only [Matrix.mulVec_add,Matrix.mulVec_smul, dotProduct_add,add_dotProduct,dotProduct_smul,smul_dotProduct, smul_add]; ring
lemma stiff_body (p q:Phase (Lines G f 1)):
    beat (F ∘ input G f) 0 2 ![p,q] = dotProduct p (Kane F *ᵥ q):=by
    let V:=F ∘ input G f
    have hv: damage (pocket (Lines G f 1)) V 0= Kbody F:=by unfold Kbody beamH; rw[show bal 1 F=V from funext fun i=>by simp[bal,V]]
    refine Leads.two (fun i=>left_beat V i) (fun i=> right_beat V i) (q:=fun p q=> dotProduct p (Kane F*ᵥ q)) (fun i u v=> ?_) (fun i u v=>?_) (fun a b=>?_) p q
    · simp [add_dotProduct]
    · simp [Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add]
    rw [beat_duo,Kane,prom_vec,p_dot]; congr 1; have hp:=detracts (pocket _) V 0 a b; rw [hv,cash_pocket,cash_pocket] at hp; exact hp.symm
lemma mail_sign (q: G.ColorIndex)(p:Site f): approached (mail (1:Config G f))*ᵥ relay p (vac,q)= ∑ i:Axis,(1-cell p (step i)) • relay p (coord i,q):=by
    let u:=approached (mail (1: Config G f))
    -- evaluate pointwise
    have hf(v:Phase (Lines G f 0))(x:Site f)(i:Axis)(j:G.ColorIndex): (u*ᵥ v) (x,coord i,j)= v (x,vac,j)-v (x+step i,vac,j):=by
       have he(v:BaseSites G f): (u*ᵥ axes v) (x,coord i,j)= axes v (x,vac,j)-axes v (x+step i,vac,j):=by
          rw [show u*ᵥ axes v=axes (cant 1 v) from (prom_vec ..).trans (congr_arg axes (mailed ..))]; change ((edgeColor (cant 1 v) (x,i) j:ℝ):ℂ) = _; rw[cant_at,Pi.one_apply,G.adjoint_one]; exact Complex.ofReal_sub ..
       refine Leads.buys (p:=fun v=>(u*ᵥ v) (x,coord i,j)) (q:=fun v=> v (x,vac,j)-v (x+step i,vac,j)) ?_ ?_ he v
       · intro a b; dsimp only; rw[mulVec_add,mulVec_smul];rfl
       intro a b;simp only[Pi.add_apply,Pi.smul_apply,smul_sub]; abel
    ext1 ⟨x,i,j⟩; obtain ⟨i,rfl⟩:=axisEquiv.surjective i; rw [Finset.sum_apply]; change (u*ᵥ _ ) (x,coord i,j)=_; rw[hf _,sum_eq_single i]; · simp [relay,tune,cell_add,Pi.single_apply];split_ifs<;>ring
    · intro a _ ha; simp [relay,tune,coord_iff,ha.symm]
    simp
omit [Fintype I] [DecidableEq I] in
lemma by_mail (U:Matrix I (Lines G f 1) ℝ)(k:G.ColorIndex)(p:Site f)(h: U*mail (1:Config G f)=0): ∑ i:Axis,(1-cell p (step i)) • (approached U*ᵥrelay p (coord i,k))=0:=by
    simp_rw [← Matrix.mulVec_smul, ← Matrix.mulVec_sum,← mail_sign,mulVec_mulVec,← prom_mul,h]; simp[approached]
lemma Kcup (hp:G.Simple)(h:Cleric F)(p:Site f)(i:G.ColorIndex): ∑ k:Axis,(1-cell p (step k)) • (Kane F*ᵥ relay p (coord k,i))=0:=by_mail _ _ _ (dyed_beam h hp)
lemma Tcup (hp:G.Simple)(h:Cloaked Y)(p:Site f)(i:G.ColorIndex): ∑ k:Axis,(1-cell p (step k)) • (Tane Y*ᵥ relay p (coord k,i))=0:=by
    refine by_mail _ _ _ (testers fun x y=>?_)
    rw [← mulVec_mulVec,mailed, Tbody,bill_pay, zero_mulVec,dyed_cant h hp y]
end YM.Trace.Lamp
