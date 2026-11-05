import YM.TraceExtension.Lamp.Rip
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ μ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W} (d i b:Axis) (q:G.ColorIndex) {F H: Maze G f}
lemma clip_far (hd:F=ᶠ[𝓝 0] H)(x y): clipP i q F x y=clipP i q H x y:=clip_eq i q ((hd.iteratedFDeriv ℝ 2).eq_of_nhds) x y
lemma lux_a (h:ContDiffAt ℝ ω F 0)(p:ContDiffAt ℝ ω H 0) : lux d i q b (F+H)= lux d i q b F+lux d i q b H:=by
    unfold lux cue;simp_rw[clip_add i q _ _ h p, mul_add]; exact map_add Deb (fun x:Dish=> _*cue _ _ q b F x) (fun x:Dish=> _*cue _ _ q b H x)
lemma lux_s (h:ContDiffAt ℝ ω F 0)(p:ContDiffAt ℝ ω H 0): lux d i q b (F-H)=lux d i q b F-lux d i q b H:=by
    unfold lux cue; simp_rw[clip_sub i q _ _ h p,mul_sub]; exact map_sub Deb _ _
lemma lux_c (t:ℝ)(h:ContDiffAt ℝ ω F 0):lux d i q b (t • F)=(t:ℂ)*lux d i q b F:=by unfold lux cue; simp_rw [clip_smul i q _ _ h t, mul_left_comm _ (t:ℂ)]; exact map_smul Deb (t:ℂ) _
lemma lux_far (hd:F=ᶠ[𝓝 0] H): lux d i q b F=lux d i q b H:=by unfold lux cue;simp_rw [clip_far i q hd]
lemma clip_total {I:Type} [Fintype I]{F:I→ Maze G f}(u v:Site f)(h:∀ i,ContDiffAt ℝ ω (F i) 0) : clipP i q (∑ i,F i) u v=∑ j,clipP i q (F j) u v:=by
    suffices hh :∀ s:Finset I, clipP i q (∑ i∈s,F i) u v=∑ j∈s,clipP i q (F j) u v from hh univ
    intro s; induction s using Finset.induction with
    | empty=> simp only[sum_empty]; simp [clipP,beat, enlarge,recording_apply]
    | insert i' t hi hp=> rw[sum_insert hi,sum_insert hi,clip_add i q _ _ (h i'),hp]; have ht:ContDiffAt ℝ ω (fun x=> ∑ j∈t,F j x) 0:=ContDiffAt.sum fun i _=>h i; rw [show (∑ i∈t,F i)=_ from (show _= (fun x=> ∑ i∈t,F i x) from funext fun x=> Finset.sum_apply ..)]; exact ht
lemma lux_t {I:Type} [Fintype I]{F:I→ Maze G f}(h:∀ i,ContDiffAt ℝ ω (F i) 0): lux d i q b (∑ i,F i)=∑ j,lux d i q b (F j):=by
    unfold lux cue; simp_rw [clip_total i q _ _ h,Finset.mul_sum]; exact (by
       let P (j:I)(x:Dish):= ((pitchf f:ℂ)⁻¹)^ (3:ℕ)*cue d i q b (F j) x
       change Deb (fun x=>∑ j,P j x)=∑ j,Deb (P j)
       rw[show (fun x=>∑ j,P j x)=∑ j,P j from funext fun i=> (Finset.sum_apply ..).symm,map_sum])
lemma cob_total {I:Type} [Fintype I]{F:I→ Maze G f}(h:∀ i,ContDiffAt ℝ ω (F i) 0): cob d i q (∑ i,F i)=∑ j,cob d i q (F j):=by
    unfold cob; simp_rw[clip_total i q _ _ h,Finset.mul_sum]; exact (by
       let P(j:I)(z:ℤ):= ((pitchf f:ℂ)⁻¹)^ (2:ℕ)*clipP i q (F j) (wrap f (ra d z)) (-(wrap f (ra d z)))
       change PanZ (fun x=>∑ j,P j x)=∑ j,PanZ (P j)
       rw [show (fun x=>∑ j,P j x)=∑ j,P j from funext fun i=> (Finset.sum_apply ..).symm,map_sum])
-- local family moving on torus
structure Traverse (V:Site f→ Maze G f): Prop where
    boot: ContDiffAt ℝ ω (V 0) 0
    pad s: V s=ᶠ[𝓝 0] V 0 ∘ rideC s
variable {A': Site f→ Maze G f}
lemma Traverse.team (h:Traverse A')(s): ContDiffAt ℝ ω (A' s) 0:= ((show ContDiffAt ℝ ω _ _ from ContDiffAt.comp (g:=A' 0) (f:=rideC s) 0 (by rw[map_zero]; exact h.boot) (rideC s).contDiff.contDiffAt)).congr_of_eventuallyEq (h.pad s)
lemma colb (h:Traverse A')(x y:Site f):clipP i q (A' x) y (-y)=clipP i q (A' 0) y (-y):=by rw[clip_far i q (h.pad _),clip_rot i q _ _ _ h.boot]; simp[cell_origin,cell_duality (0:Site f)]
lemma cob_in (h:Traverse A')(x): cob d i q (A' x)=cob d i q (A' 0):=by unfold cob; simp_rw[colb i q h]
lemma cob_s_tot (h:Traverse A') : cob d i q (∑ i,A' i)=(Fintype.card (Site f):ℂ)*cob d i q (A' 0):=by rw[cob_total d i q h.team,Finset.sum_congr rfl (g:=fun _=>cob d i q (A' 0)) (fun x _=>cob_in d i q h x),sum_const,card_univ,nsmul_eq_mul]
-- SBP step for anchor 0. taps. Needs only f germ under shift. book uses ∆ = elms
lemma Rose.sumX {X:Type}[NormedAddCommGroup X]{I:Type*}(s:Finset I){F H:I→ W→X}(h:∀ i∈s,Rose L (F i) (H i)) : Rose L (fun x=> ∑ i∈s,F i x) (fun x=>∑ i∈s,H i x):=by
    induction s using Finset.induction with
    | empty=> simp_rw [sum_empty]; exact Rose.const _
    | insert i s hi ih=> simp_rw[sum_insert hi]; exact Rose.inc (h _ (mem_insert_self ..)) (ih fun i hi=> h _ (mem_insert_of_mem hi))
variable (Q:Tendsto (fun w=>(g w).val) L atTop){V:∀ w,Site (g w)→Maze G (g w)}(h:Pico (fun _=>0) (fun w=> V w 0) 2) (hp:∀ i, Traverse (V i))
include Q h hp
lemma orb_pick (x:Cover): Rose L (fun w=> lux d i q b (V w (wrap (g w) x)-V w 0)) (fun w=> -(x b:ℂ)* cob d i q (V w 0)):=
    Rose.chain (Rose.skip (Eventually.of_forall (fun j=> lux_far d i b q ((hp j|>.pad (wrap (g j) x)).sub EventuallyEq.rfl)))) (ride_l d i b q Q (fun w=>V w 0) h x)
lemma orb_debit (a:Axis): Rose L (fun w=> lux d i q b (elm a (V w) 0)) (fun w=> if a=b then -cob d i q (V w 0) else 0):=by
    let S(j:Fin 4):Cover:= Pull.steps j • step a
    let A(w)(j:Fin 4):= V w (wrap (g w) (S j))-V w 0; let B(w)(j:Fin 4):= V w (wrap (g w) (-S j))-V w 0
    have hx(w): elm a (V w) 0= ∑ j:Fin 4, (Pull.cash j) • (A w j-B w j):=by
        unfold elm Pull.dTap; refine sum_congr rfl fun j _=> ?_; unfold A B S; rw[map_neg,map_nsmul,wrap_step]; simp
    have hu(w j):ContDiffAt ℝ ω (A w j) 0:= by unfold A; exact ((hp w).team _).sub ((hp w).team _)
    have hv(w j):ContDiffAt ℝ ω (B w j) 0:= by unfold B; exact ((hp w).team _).sub ((hp w).team _)
    have hf: (fun w=>lux d i q b (elm a (V w) 0))=(fun w=>∑ j,(Pull.cash j:ℂ)*(lux d i q b (A w j)-lux d i q b (B w j))):=by
        ext1 w; rw [hx,lux_t];swap; · exact fun j=> ((hu w j).sub (hv w j)).const_smul (Pull.cash j)
        refine sum_congr rfl fun j _=>?_ ; rw [lux_c d i b q _ (F:= (A w j-B w j)) ((hu w j).sub (hv w j)), lux_s d i b q (F:= A w j) (H:= B w j) (hu w j) (hv w j)]
    rw[hf]; refine Rose.chain (Rose.sumX _ (F:=fun j w=> _* (_-_)) (fun j _=>roseRate (Pull.cash j:ℂ) (Rose.dec (orb_pick d i b q Q h hp (S j)) (orb_pick d i b q Q h hp (-(S j)))))) ?_
    apply Rose.skip (Eventually.of_forall fun w=>?_); let x:= cob d i q (V w 0)
    change ∑ j,(Pull.cash j:ℂ)*(-((S j b:ℤ):ℂ)*x- -((((-(S j)) b:ℤ):ℂ))*x)=_
    unfold S; split
    next he=> subst b
              have h:=Pull.credit 1 (by omega); simp only [pow_one,sub_neg_eq_add,if_true] at h
              have ht: ∑ x,(Pull.cash x:ℂ)*((Pull.steps x:ℂ)+(Pull.steps x:ℂ))=1:=by exact_mod_cast h
              rw[show -cob d i q (V w 0)= (∑ x,(Pull.cash x:ℂ)*((Pull.steps x:ℂ)+(Pull.steps x:ℂ)))*(-x) from by rw[ht,one_mul],Finset.sum_mul]; refine sum_congr rfl fun j _=>?_ ; simp [nsmul_eq_mul];ring
    next he=> have hh:(step a:Cover) b=0:=by simp [Ne.symm he]
              simp only [Pi.smul_apply,hh,smul_zero,Pi.neg_apply,neg_zero,Int.cast_zero,zero_mul,sub_zero,mul_zero,sum_const_zero]
end YM.Trace.Lamp
