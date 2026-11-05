import YM.OPE.Nesting.Moving

/-!
# Fee for common readouts of an exchangeable array

The *linear reader*, even on a collection of alternatives with completely
different slot types, charges the same shell discrepancy. The reason is not
invariance of the detector constellation under the rotation itself. Instead
all its swept points are admissible finite exterior tests of the true moment;
weak comparison estimates are uniform along arbitrary such sweeps after the
desired refinement. The polarized basis remains one system as in item I.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Sensor
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
attribute [local instance] Orbits.measO Orbits.borelO Orbits.hμ
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
variable {L I:Type} {l:Filter L}{a:L→ℝ}{o:L→E4}{z:L→I→E4}
local notation "P₀" => R.port
local notation "Q" => U.sector.derivatives
local notation "X" => U.sector.turns
local notation "ρ" => U.room.kernel.spin

def portW (e:Exterior C.book):ℝ := weight (expo e)

def affordable (m:ℕ)(W:ℝ) : Prop:= ∀ k∈bands Q m,∀j∈ (R.port.sheet k).support,portW j ≤ W
lemma roomFor (D:ℕ): ∃ W,∀m≤D,affordable U R m W:=by
    let V:= (bands Q D).biUnion (fun k=>(R.port.sheet k).support)
    have hv:= (V.image portW).finite_toSet.bddAbove
    obtain ⟨v,h⟩:=hv; refine ⟨v,fun m hm k hk j hj=>h (Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ?_))⟩
    refine ⟨k, full_bands .. |>.mpr (?_),hj⟩; exact (full_bands Q k |>.mp hk).trans hm

include R
lemma zero_spin (n:ℕ) (p:E4)(k:Ortho):spinning P₀ X n (sole p) p k ((sole (0:S.Field 0)):Labels S (fun _:Unit=>0)) = 0:=by
   rw [scatter P₀ R.continuum]
   apply Finset.sum_eq_zero fun i hi=>?_
   unfold bears; rw [MultilinearMap.map_coord_zero _ () ?_, zero_smul]
   apply map_zero (U.sector.turns.act 0 k⁻¹)

lemma marginTerm [Fintype I]{b:ℝ}{A:Menu S L}(q:A.Draw)(g:Eligible l a z b A) (h:Tendsto (fun i=>away (z i) (o i)) l (𝓝 0))(n:ℕ): ∀ᶠ s in l, orbitMargin P₀ n ((A.pick q).place s) (o s) :=by
   refine eventually_dock P₀ ?_ (g q).2.1.inject n
   obtain ⟨φ,hφ⟩:=(g q).1; rw [hφ]; exact shrink_comp h φ

variable [Fintype I] {b:ℝ}

lemma toSensors (hA:Tendsto a l atTop)(h:Tendsto (fun i=>away (z i) (o i)) l (𝓝 0))(hb:0≤b)(k:L→Ortho)(e:Exterior C.book):Intervals l a b z (fun i=>swung e (k i) (o i)) :=by
     have h':∀ᶠ c:ℝ in 𝓝[>]0,∀ j,c < ‖bearing e j‖ := eventually_all.mpr fun j=> (gt_mem_nhds (show 0 < ‖bearing e j‖ from norm_pos_iff.mpr ((beside_distinct.mp (bearing_clear e)).2.2 () j).symm)).filter_mono nhdsWithin_le_nhds
     obtain ⟨c,hc,hh⟩:=h'.and (show ∀ᶠ c:ℝ in 𝓝[>]0,0<c from self_mem_nhdsWithin) |>.exists
     refine bounded_interval hA h ⟨c,hh,Eventually.of_forall fun i _ j=> (hc j).trans_eq ?_⟩ |>.mono hb
     change ‖bearing e j‖ = ‖o i-(o i+Ortho.move (k i) (bearing e j))‖; rw [sub_add_cancel_left,norm_neg,Ortho.move_norm]

variable (A A':Menu S L)
def rotAtom (A:Atom S L) (m:ℕ)(o:L→E4)(s:L)(k:Ortho):S.Field m:= A.amp s • spinning P₀ X m (A.place s) (o s) k (voices A.tags)
def deposit (A:Menu S L)(m:ℕ)(o:L→E4)(s:L)(k:Ortho):= ∑ t:A.Draw, rotAtom U R (A.pick t) m o s k

def avgAtom (A:Atom S L)(m:ℕ)(o:L→E4)(s:L):S.Field m:= A.amp s • averageV P₀ X m (A.place s) (o s) (voices A.tags)
def avgMenu (A:Menu S L)(m:ℕ)(o:L→E4)(s:L):= ∑ t:A.Draw, avgAtom U R (A.pick t) m o s

omit R in
private lemma charge_weight (e:Exterior C.book)(k:Ortho): weightOf (chars (turnsPort X k e))=portW e:=rfl
variable {m:ℕ}{o:L→E4}{s:L}{k:Ortho}
lemma spin_atom {A:Atom S L}(h:orbitMargin P₀ m (A.place s) (o s)): rotAtom U R A m o s k = ∑ e∈bands Q m,∑ j∈(R.port.sheet e).support, ((R.port.sheet e) j * A.sample (fun _=>S) (fun t=>swung j k (o t)) (chars (turnsPort X k j)) s) • U.sector.turns.act _ k (R.port.loaded e m) :=by
   have he:= discrepancy_spin (x:=A.place s) (k:=k) R.port R.law R.continuum U.phase.transport.motion (voices A.tags) (0:S.Field 0) h
   rw [zero_spin, sub_zero] at he
   simp only [discrepancy,map_zero,sub_zero,Finset.sum_smul] at he
   unfold rotAtom; rw [he,Finset.smul_sum]; refine Finset.sum_congr rfl fun i hi=>?_
   rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j hj=>?_
   unfold sample duet; rw [smul_smul]; exact congr_arg (· • _) (mul_left_comm ..)
lemma spin_sum (h:∀ c:A.Draw,orbitMargin P₀ m ((A.pick c).place s) (o s)): deposit U R A m o s k= ∑ e∈bands Q m, ∑ j∈(R.port.sheet e).support, ((R.port.sheet e) j * A.atView (fun _=> S) (fun t=>swung j k (o t)) (chars (turnsPort X k j)) s) • U.sector.turns.act _ k (R.port.loaded e m):=by
   unfold deposit Menu.atView
   have hp(c:A.Draw):rotAtom U R (A.pick c) m o s k= _:=spin_atom U R (h c)  
   simp_rw [hp,Finset.mul_sum,Finset.sum_smul]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i hi=>?_; rw [Finset.sum_comm]
lemma integrate_atom (A:Atom S L)(h:orbitMargin P₀ m (A.place s) (o s)): Integrable (rotAtom U R A m o s) haar ∧ ∫ k,rotAtom U R A m o s k ∂haar = avgAtom U R A m o s:=by
    unfold avgAtom rotAtom; rw [Orbits.averageV,if_pos h]
    constructor; swap; · exact integral_smul ..
    apply Integrable.smul (A.amp s) (f:=fun k=>spinning P₀ X m _ _ k _) ?_
    simp_rw [scatter P₀ R.continuum]; refine integrable_finsetSum _ (fun i hi=>integrable_bears P₀ R.law R.continuum m _ _ _ _ (h i hi))
set_option maxHeartbeats 800000 in
lemma integrate_sum (A:Menu S L)(h:∀ t:A.Draw,orbitMargin P₀ m ((A.pick t).place s) (o s)) : Integrable (deposit U R A m o s) haar ∧ ∫ k,deposit U R A m o s k ∂haar = avgMenu U R A m o s:=by
    let f := fun i=> rotAtom U R (A.pick i) m o s
    have hf(i:A.Draw): Integrable (f i) haar:= (integrate_atom U R _ (h i)).1
    change Integrable (fun k:Ortho=>∑ i,f i k) haar ∧ ∫ k:Ortho, (∑ i,f i k) ∂haar=avgMenu U R ..
    exact ⟨integrable_finsetSum (f:=f) _ (fun i _=>hf i), (integral_finsetSum (f:=f) _ (fun i _=>hf i)).trans (Finset.sum_congr rfl (fun i _=>(integrate_atom U R _ (h i)).2))⟩

variable {u W γ:ℝ}

set_option maxHeartbeats 500000 in
lemma ink (A A':Menu S L)(h: ∀ e∈bands Q m,∀ j∈ (R.port.sheet e).support, portW j ≤ W →∀k:L→Ortho,RateLE l a (fun s=> A.atView (fun _=> S) (fun t=>swung j (k s) (o t)) (chars (turnsPort X (k s) j)) s-A'.atView (fun _=> S) (fun t=>swung j (k s) (o t)) (chars (turnsPort X (k s) j)) s) γ) (hw:affordable U R m W)(hA:Tendsto a l atTop) (h₁:Eligible l a z b A)(h₂:Eligible l a z b A')(hz:Tendsto (fun i=>away (z i) (o i)) l (𝓝 0)) : RateLE l a (fun s=>avgMenu U R A m o s-avgMenu U R A' m o s) γ:=by
   let dq(s:L)(k:Ortho):S.Field m:=deposit U R A m o s k-deposit U R A' m o s k
   have hE : ∀ᶠ s in l, (∀q, orbitMargin P₀ m ((A.pick q).place s) (o s)) ∧ ∀q, orbitMargin P₀ m ((A'.pick q).place s) (o s):=(eventually_all.mpr fun q=>marginTerm U R q h₁ hz _).and (eventually_all.mpr fun q=>marginTerm U R q h₂ hz _)
   refine (price_integral (μ:=haar) dq ?_).congr (hE.mono fun s ⟨hs,ht⟩=>?_)
   swap
   · obtain ⟨hp,hq⟩:=integrate_sum U R A hs; obtain ⟨hp',hq'⟩:=integrate_sum U R A' ht
     change ∫ k, dq s k ∂haar= _; exact (integral_sub hp hp').trans (congr_arg₂ (·-·) hq hq')
   intro k; let μ:Ortho→L→ Exterior C.book→ℂ := fun k s j=> A.atView (fun _=> S) (fun t=>swung j k (o t)) (chars (turnsPort X k j)) s-A'.atView (fun _=> S) (fun t=>swung j k (o t)) (chars (turnsPort X k j)) s
   have hp(e)(he:e∈bands Q m)(j)(hj:j∈(R.port.sheet e).support): RateLE l a (fun s=>((R.port.sheet e) j * μ (k s) s j) • U.sector.turns.act m (k s) (R.port.loaded e m)) γ:= (((RateLE.const _ hA).mul (h e he j hj (hw e he j hj) k)).smul (loaded_rate hA P₀ R.law m e k)).mono (by rw [zero_add,add_zero])
   refine (RateLE.sum (S:=bands Q m) hA (fun e he=>(RateLE.sum hA fun j hj=>hp e he j hj))).congr (hE.mono fun s ⟨hs,ht⟩=>?_); dsimp only; symm; change dq s (k s) = _
   unfold dq; rw [spin_sum U R A hs,spin_sum U R A' ht,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl fun i hi=> ?_; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl fun j hj=>by rw [← sub_smul]; apply congr_arg (· • _) (mul_sub .. |>.symm)
end YM.OPE.Nesting.Sensor
