import YM.RG08.Orison.Law

/-! # Kinetic farm at infinite regulator. Known not by differentiating
 cutoff limits but by rooted stencil stability. Horizon & Recitation checks. -/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen Rows
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}

lemma branching (G:Gauge)(e n:ℕ): demand (Yamen.top G) e n=if h:n=e+2 then Steam.move h.symm (Crown.recitation G e) else 0:=by
 unfold demand Yamen.top
 by_cases h:n=e+2
 · subst n; rw [dif_pos rfl]; unfold Steam.move Crown.recitation
   have he(i j:ℕ)(hi:i∈range (e+1))(hj:j∈range (i+1)): RG08.Mount.flight j i (if i=j∧Even i then Crown.prize G (RG08.Mount.rank j) else 0) e (e+2) = if j=i then (if Odd (i+2) then 0 else Carrel.completed (Crown.prize G (i+2)) 0 (e+2)) else 0:=by
       by_cases hk:j=i;swap
       · rw [if_neg (fun h=>hk h.1.symm),if_neg hk,Sedan.flight_nil]
       subst j; simp only [true_and,↓reduceIte]; by_cases h:Even i
       · rw [if_pos h,if_neg (Nat.not_odd_iff_even.mpr (h.add (by decide))),RG08.Mount.flight,if_pos ?_]
         · rfl
         simp only [mem_range] at hi;unfold RG08.Mount.rank;omega
       rw [if_neg h,if_pos (by exact (Nat.not_even_iff_odd.mp h).add_even (by decide)),Sedan.flight_nil]
   let f(i:ℕ):Flake (e+2) (Market (Loc G 1)):= if Odd (i+2) then 0 else Carrel.completed (Crown.prize G (i+2)) 0 _
   rw [show _=(∑ i∈range (e+1),f i) from Finset.sum_congr rfl (by intro i hi; rw [Finset.sum_congr rfl (fun j hj=>he i j hi hj),sum_ite_eq'];simp +contextual [f])]
   change (∑ i∈range (e+1),f i)=Crown.recitation G e
   unfold Crown.recitation; conv_rhs=>rw [sum_range_succ',sum_range_succ']
   simp only [true_or,dif_pos,show Odd (0+1:ℕ) from by decide,or_true, add_zero]; apply sum_congr rfl;intro i _;unfold f; by_cases hh:Odd (i+2) <;> first|rw [if_pos hh,dif_pos (by right;exact hh)]|(rw [if_neg hh,dif_neg (by rintro (ha|ha); omega; exact hh ha)]; rfl)
 rw [dif_neg h];apply Finset.sum_eq_zero; intro i hi;apply Finset.sum_eq_zero;intro j _;split
 next H=>have hv:i=j:=H.1; unfold RG08.Mount.flight;rw [if_neg (by simp only [mem_range] at hi; unfold RG08.Mount.rank;omega)]
 next=>exact Sedan.flight_nil ..

lemma kinetic {E:ℕ}{X:ℕ→Castle G}{V:Castle G}(hg:G.Simple)(h:Shade E X V){e:ℕ}(he:e ≤ E){p:ℝ}(hX:∀ᶠ i:ℕ in atTop,Loop.Core (X i 0 e) p):Loop.Core (V 0 e) p:=by
 have hf := metered hg h e he
 have hM: Loop.reading (V 0 e) hg (1/2)= p/(1/2):= tendsto_nhds_unique hf (Tendsto.congr' (f₁:=fun _=>p/(1/2:ℝ)) (hX.mono fun i hi=>by change p/_ = _/_;rw [Loop.measured _ hg hi]) tendsto_const_nhds)
 have hx:Loop.measure (V 0 e) hg=p:=by unfold Loop.reading at hM; linarith
 obtain ⟨H,s,c,hs,hc,Hx⟩:=h.valid.honor 0 e
 exact hx ▸ Loop.plays hg hs.le hc H Hx

variable {G:Gauge}{a:Levels G}{F:Horizon a}{P X:MapPrices}(hg:G.Simple){Z:ChartRatio G}{U:ℕ→Kernel Flat.Links Flat.Links}{A B c:ℝ}{d k:ℕ}{E:ℕ}
variable (L: Yamen.Supplies F P Z)(hM:Bill G P X a)(hh:Payment G P X Z a)(hA:Flat.Quorum (Flat.curve X) U 0 F A B d k c)
include L hM hh hA
set_option warningAsError true
lemma stage (i:ℕ)(he:E ≤ a.clock.J i):
    let V:=report F P X hg Z E i;let U:=issue F P X hg Z E i
    ; let w:=torque U hg
    ; w 0=1∧ Loop.Core (V 0 0) (1/2) ∧ Loop.Core (U 0 0) (1/2) ∧ (∀ e, e≠0→Loop.Core (V 0 e) 0) ∧ ∀ n k,k ≤ n → coeff k ((Nacre.ratio w)^2)=coeff k (1+∑ j∈(Nacre.square n).erase 0,Nacre.factor w (Nacre.ratio w) j):=by
 intro V U w
 have H:= fidelity (F:=F) hg L hM hh hA i (i+1) (Nat.le_succ i) he
 have Hx:= Orison.honesty (F:=F) hg L hM hh hA i (i+1) (Nat.lt_succ_self i) he
 have heY(n:ℕ):= ship (F:=F) X hg L (N:=n+(i+1)) (i:=i) (by omega)
 have hf:Loop.Core (V 0 0) (1/2):= kinetic hg H (Nat.zero_le E) (Eventually.of_forall (fun n=> (heY n).origin.main))
 have ht:Loop.Core (U 0 0) (1/2):=kinetic hg Hx (Nat.zero_le E) (Eventually.of_forall (fun n=> (veils (X:=X) L.housed (n+(i+1)) i hg (by omega) (fun _=> L.herald _ _ _ (by omega:i ≤ n+(i+1)))).1.main))
 refine ⟨?_,hf,ht,?_,fun n k hk=>Nacre.guaranteed w hk⟩
 · unfold w torque Loop.reading;rw [Loop.measured _ _ ht];norm_num
 intro e hE;by_cases he0:e ≤ E
 · exact kinetic hg H he0 (Eventually.of_forall (fun i=>(heY i).cure e hE))
 have hx:V 0 e=0:=by unfold V report Orison.erase;rw [if_neg (by rintro ⟨h,_⟩;exact he0 h)]
 rw [hx]; intro a b _ _ t; unfold Loop.spectrum Loop.AxisK Loop.load Loop.col hum; dsimp only [Pi.zero_apply];simp

-- Compatible horizons: formation admissible only at both origins before phase proofs. Names don't bake E into coefficients.
omit L hM hh hA in
theorem horizons (E e:ℕ) (i:ℕ) (h:e ≤ E):report F P X hg Z e i=Orison.erase e (report F P X hg Z E i) ∧ issue F P X hg Z e i=Orison.erase e (issue F P X hg Z E i):=by
 constructor <;> ext r n x <;> first | unfold report Orison.erase| unfold issue Orison.erase
 all_goals split_ifs <;> first| rfl| grind
end YM.RG08.Orison
