import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Coupons
/-!
# Adapt growth argument in Next/RANK/ShapeS etc

Here on weaker Novice. Don't need to change Crew requirements or costs. For
claims independent of the actual representation/heating
reuse those on a strong F at windows where able (see Spire).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Next.Rank Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V Ω : Type*}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points m} {hk : i≤k} {hi : middle C.path.levels b k ≤ i}
variable {c : Course C N p k}
variable {ξ : Purse}

lemma Novice.small {L' : Rep G (C.side i p)} (hx : i≤N) (h : Novice c i L' hx) : L'.p.threshold / anneals C c i ≤ torque (clim C.path.levels i) := by
  obtain ⟨σ,g,Λ,δ,w,he,hp⟩:= h.chand.proper
  let s:= clim C.path.levels i;let a:= Vac.Numbers.Hat s; let b:=torque s
  have hC:0<s:= zero_lt_one.trans (C.path.levels.fits.delayed _); have hf:0<a:=by unfold a Vac.Numbers.Hat; positivity
  have hg:= warmth C c hx; let r:=anneals C c i
  have ht : L'.beta*r^2=1:= by
    have hz:= c.pos i hx
    unfold r anneals; rw [inv_pow,Real.sq_sqrt hz.le,← h.chand.tied.coupling,mul_inv_cancel₀ hz.ne']
  have hV : a^2*s=1:= by unfold a Vac.Numbers.Hat; rw [inv_pow,Real.sq_sqrt hC.le,inv_mul_cancel₀ hC.ne']
  rw [h.threshold]; apply (div_le_iff₀ hg).mpr
  have hx : a ≤ 2*r:= by
    apply (le_of_pow_le_pow_left₀ two_ne_zero (show 0 ≤ 2*r by exact mul_nonneg (by norm_num) hg.le))
    apply le_of_mul_le_mul_right _ hC; calc
      _ = L'.beta * r^2:= hV.trans ht.symm
      _ ≤ (4*s)*r^2:= mul_le_mul_of_nonneg_right he.cap (sq_nonneg _)
      _ = _ := by ring
  change a* hot s≤ torque s*r
  unfold torque; linarith only [mul_le_mul_of_nonneg_right hx (show 0 ≤ hot s from (Real.exp_pos _).le), mul_nonneg (show 0≤r from hg.le) (show 0≤ hot s from Real.exp_pos _|>.le)]

section
variable (X : AtlasData G C.S p) (F : Lead G C.S p)
section
variable {P : Rep G (C.side k p)} (W : StampDuty C k N p d ξ.taylor P ξ.era.coast.Q X)
variable (Y : Corridor C.path.levels b ξ k) (v : Fin m→ C.label d)
variable (O : KFlux (C:=C) k (middle C.path.levels b k) X ξ F)
variable (Z : ∀ i, coin (W.W (v i))≤ ξ.principal (clim C.path.levels k))
include Y
variable (i : ℕ) {Q : Rep G (C.side i p)} (R : ReadySh (A:=C.path.levels) b X ξ.horizon ξ.era.coast.Q k F) (x : Points m)
variable (hk : i≤k) (h : middle C.path.levels b k ≤ i) (c : Course C N p k)
include Z O
lemma v_radiant_mimic (hn : m≤2) (he : Novice c i Q (hk.trans c.allow)) :
    let t:= clim C.path.levels k
    let s:=mimics x v W R c.allow hk h (anneals C c i)
    Shine s Q.p (fun _=>ξ.cash t) (load ξ.era) (Perch.bill (-4) t) := by
  intro t s
  let r:=ξ.cash t; let e:=load ξ.era;let M:= torque t
  let B:=walls (clim C.path.levels i); let q:=ξ.era.coast.Q
  have hW : principle C Q.p c.allow x b hk q ξ.horizon p s:= by intro j; have ht : Q.p.B= B:= he.budget; rw [ht];exact ⟨rfl,rfl⟩
  let C':= rentQ q e
  have hu : 0≤ C':= (Real.exp_pos _).le
  let α:= C'*Perch.bill (-6) t
  have h₁ : 0 ≤ α:= mul_nonneg hu (Real.exp_pos _).le
  apply per_word s hW hn h₁ r e _ ?_ Y.spend.venue; intro j
  let f:= jacketPol (F:=F) (s:=b) x v W hk j.2.val; let u:= (s j).fires
  have hv:= vertex_cap X F W Y v O Z i hk x h j.2.val
  have hx: 0<r:= Real.exp_pos _
  refine ⟨h₁,fun U hU=>?_⟩; let l:= (basisK c x b i c.allow hk h j.1 j.2.val U)
  change Value.charge Q.p e (s j).extent * Poly.toll (fun _=>r) u * ‖dot _ (text (rigid l) f)‖ ≤ α
  have hC : Value.charge Q.p e (s j).extent ≤ C':= by rw [(hW _).1]; exact hall q Q.p (add_nonneg ξ.era.coast.base (by norm_num))
  rw [mul_assoc,dot_norm]; refine mul_le_mul hC ?_ (mul_nonneg (Poly.worth (fun _=> hx) _).le (norm_nonneg _)) hu
  have hh : Healthy Q.p.threshold (dolmens x b q B c.allow hk j.1 j.2.val) U:=hU
  have hp : ∀ i'∈ f.vars, |rigid l i'|≤ M:= by
    intro i' hφ
    have ha' : separation (core _ _ _ _ hk _) _≤ (ξ.horizon+8)*B:= (premise x v W R hk h j.2.val).2 i' hφ
    apply (rigidHelm _ _).trans
    exact (insured R.canvas h hk j.1 i' U ha' hh).trans ((Novice.small _ he).trans (Y.spend.lots _ (Y.court i ((Station.wider ..).trans h) hk)))
  have hZ : ‖text (rigid l) f‖≤ coin f* Perch.bill 1 t:= (view_v _ _ hv.2 Y.spend.calm hp).trans (mul_le_mul_of_nonneg_left Y.spend.primers (Rise.sign _ _ zero_le_one))
  apply (mul_le_mul_of_nonneg_left hZ (Poly.worth (fun _=>hx) _).le).trans; rw [mul_left_comm,← mul_assoc]
  have hU:u.val.card=(tale j.2.val).val.val.card:= by change ({j.1}×ˢ(tale _).val.val).card=_;rw [card_product,card_singleton,one_mul]
  unfold Poly.toll; rw [prod_const,hU]; rcases j with ⟨j,⟨w|V,hc⟩⟩
  · have hp:coin f≤ ξ.ledger t:=hv.1
    rw [show _ = 1 from (show (tale (.inl w)).val.val.card=1 from card_singleton _), pow_one]; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hx.le) (Real.exp_pos _).le).trans (incomeR1 ..)
  have hp:coin f≤ξ.double t:= hv.1
  rw [show _ = 2 from (show (tale (.inr V)).val.val.card=2 from card_pair V.property.ne)]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (sq_nonneg r)) (Real.exp_pos _).le).trans (incomeR2 ..)
end

end
variable {P : (i : ℕ) → Rep G (C.side i p)} {X : AtlasData G C.S p}
variable (F : Nylon c P X R ξ)
include F in
lemma v_alignment (h : Corridor C.path.levels ξ.band ξ k) (hm : middle C.path.levels ξ.band k ≤ j) (hk : j<k) :
    let s:=clim C.path.levels k
    Metal ξ.band c R hk (ξ.sends s) (P (j+1)).p.threshold (P j).p.threshold (knox s) (torque s) ξ.L:= by
  intro s; let A:=C.path.levels;let u:= (show middle A ξ.band k≤ j+1 from hm.trans (Nat.le_succ _))
  have ht(i : ℕ) (he : middle A ξ.band k ≤ i) (hv : i ≤ k) : (P i).p.threshold / anneals C c i ≤ torque s := (Novice.small _ (F.fixture he hv)).trans (h.spend.lots _ (h.court _ ((Station.wider ..).trans he) hv))
  exact ⟨F.paths.withers j hm hk,(F.probes.steps j hm hk).pay,Glimmer.costed _ _ zero_le_one,h.spend.calm,(ht _ u hk).trans h.spend.inside, ht _ hm hk.le,h.spend.transverse,h.spend.budget,F.probes.realPath _ hm hk⟩

variable (O : StampDuty C k N p d ξ.taylor (P k) ξ.era.coast.Q X)
variable (v : Fin m→ C.label d)
variable (H : Corridor C.path.levels ξ.band ξ k) (he : Fit C.path.levels ξ.band k x)
variable (hn : m≤2) (Hv : Crew c P R ξ x)

-- passage at fixed F, x,v; W forecast includes all R.Inc budgets already accumulated

def v_carried (H' : middle C.path.levels ξ.band k ≤ i) (hh : i≤k) : Prop:=
    let A:= C.path.levels; let s:=clim A k; let X:=mimics x v O F.paths c.allow hh H' (anneals C c i)
    marche ξ.band c.allow hh (P i) c x v ξ.horizon X (ξ.cash s) (load ξ.era) (ξ.epoch s (k-i)) (Perch.gas ξ.era.coast (clim A i))

include H he hn Hv F
lemma v_paf (M : ∀ u,coin (O.W (v u))≤ ξ.principal (clim C.path.levels k)) (h : middle C.path.levels ξ.band k ≤ i) (hp : i<k)
    (hz : v_carried (x:=x) F O v (h.trans (Nat.le_succ i)) (show i+1≤ k from hp)) : v_carried (x:=x) F O v h hp.le:= by
  let A:=C.path.levels;let p':=P (i+1);let Q:=P i;let s:= clim A k; let s':=clim A i;let u:=h.trans (Nat.le_succ i); let y:=ξ.cash s;let r:=ξ.era.coast; let ε:=ξ.sends s
  let j:=i+1;let hj:j≤k:=hp; let W:= mimics x v O F.paths c.allow hj u (anneals C c j); let L:= mimics x v O F.paths c.allow hp.le h (anneals C c i)
  let z:= ξ.epoch s (k-j); let e:=load ξ.era; let β:=ξ.era
  obtain ⟨Lr,H'⟩:=Hv.ignition i hp h; have hC := F.fixture u hj; have hC':=F.fixture h hp.le
  have hW : Shine W p'.p (fun _=>y) e (bill (-4) s):= v_radiant_mimic X R O H v F.probes M j F.paths x hj u c hn hC
  have hP : principle C p'.p c.allow x ξ.band hj r.Q ξ.horizon p W:= by
    intro i; rw [show p'.p.B = walls (clim A j) from hC.budget];exact ⟨rfl,rfl⟩
  have hpL : principle C Q.p c.allow x ξ.band hp.le r.Q ξ.horizon p L:= by
    intro a; rw [show Q.p.B= walls (clim A i) from hC'.budget];exact ⟨rfl,rfl⟩
  obtain ⟨ι,κ,ha,hb,G,K,h₀,hB,h₁⟩:= hz;
  have hht := H.races.pos (Nat.sub_le_sub_left u k); have hy': ξ.demand s ≤ z:=ξ.profit _ _
  have hy:0 ≤ z:= le_trans (Real.exp_pos _|>.le) hy'
  obtain ⟨α,φ,ψ,hl,hQ,hS,Q₁,Q₂,Q₃,H₀,hx,hK,h₂,h₃,hD,h₄⟩:= H'.lump W hP hW z hy hht.2 ι κ ha hb G K h₁ hB
  let x':=H.court i ((Station.wider ..).trans h) hp.le; let f:= jacketPol x v O hj (F:=R) (s:=ξ.band)
  obtain ⟨hs₁,hs₂,hm⟩:= H.spend.voice s' x'; let w:= knox s; let δ:=grant w ε (ξ.double s) (2*ξ.taylor)
  have hg a:= vertex_cap X R O H v F.probes M j hj x u a
  have hh z U (hpV : Healthy Q.p.threshold (dolmens x ξ.band r.Q Q.p.B c.allow hp.le z.1 z.2.val) U): ‖(∑ t,if (Q₂ t).fires=(L z).fires then (Q₂ t).value U else 0) - (L z).value U‖ ≤ δ:= by
    rw [(hpL _).2,h₄ z U hpV];
    have hy: ε ≤ 1:= by unfold ε Purse.sends; exact (Glimmer.billed _ (neg_nonpos.mpr ξ.positive)).trans (by simp [bill])
    have hp':= premise x v O F.paths hj u
    let P₀:= fun a => prefaced O (v a) (Station.choose A ξ.band k x a)
    apply console (Lr.tag z U hpV) hn f P₀ (by apply Disjoint.mono_left _ hpV; exact (congr_arg (fun x'=> dolmens (C:=C) x ξ.band r.Q x' c.allow hp.le z.1 z.2.val (p:=p)) hC'.budget.symm).le) F.paths.canvas (v_alignment F H h hp) (Real.exp_pos _) hy rfl
      (fun j=>(hp' j).1) ?_ (fun j=> (hg j).2) (fun j=> (hp' j).2) (falters x v O F.paths hj u)
    rintro (i|i)
    · exact (hg _|>.1|>.trans (ξ.ledger_lo _))
    exact (hg _).1
  let Y:= bill (-1) s; let Z:= Paint.trib r.a s'
  have hhZ:0 ≤ Z:=mul_nonneg r.posA.le (by positivity)
  have hδ:0≤ δ:= by
    have hu:= Tapes.grantNonneg w ε (ξ.double s) (2*ξ.taylor) (Glimmer.costed _ _ zero_le_one) (Real.exp_pos _).le (Real.exp_pos _).le; exact hu
  obtain ⟨ι',κ',hl',hm',H'',K',hp₂,hv,hΩ⟩:=resumeP Q L Q₁ Q₂ Q₃ hpL hn he H.heft h F.paths.canvas hC'.budget h₃ H₀ h₂
    (Real.exp_pos _).le (Real.exp_pos _ : 0<y) (ξ.cash_le _) (show 0≤ e from add_nonneg r.base (by norm_num)) hx hK (Real.exp_pos _ : 0<Y).le hhZ hs₁ (hC'.budget.symm ▸ hs₂) hh hδ
  refine ⟨ι',κ',hl',hm',H'',K',?_,hv,?_⟩; let γ:= Issued C ξ.band x c.allow p v
  · rw [Course.flow_step c _ i (lt_of_lt_of_le hp c.allow),h₀]; exact Eq.trans hD hp₂
  have hR : z≤ bill (-4) s:= hht.2
  have hu : Perch.gas r s'=Real.exp (-Z):= by unfold Perch.gas Z Paint.trib; ring_nf
  refine ⟨Shine.loose (show Shine _ _ _ _ _ from hΩ.bulk) ?_, Stripes.loose (show Stripes _ _ _ _ (Real.exp (-Z)*(Real.exp Y-1)) from hΩ.forced) ?_⟩
  · change β.α*z+ξ.demand s+4*(rentQ β.coast.Q (load β)*δ) ≤ ξ.epoch s (k-i)
    have hw : ξ.epoch s (k-i)=(β.α+2)*z:= by
      unfold Purse.epoch Purse.race z β; rw [show k-i=k-j+1 from by dsimp [j];omega,pow_succ]; dsimp only [Purse.epoch,Purse.race];ring
    rw [hw]; linarith only [hy',H.spend.paper]
  exact (mul_le_of_le_one_right (Real.exp_pos _).le hm).trans_eq hu.symm

lemma v_keptUp (M : ∀ u,coin (O.W (v u))≤ ξ.principal (clim C.path.levels k)) (hL : v_carried (x:=x) F O v (before ..) (le_refl k)) :
    v_carried (x:=x) F O v (le_refl (middle C.path.levels ξ.band k)) (before ..) := by
  let l:= middle C.path.levels ξ.band k
  have H' (z : ℕ) (hz : z≤k) (hf : l≤ z) : v_carried (x:=x) F O v hf hz:= by
    induction hz using Nat.decreasingInduction with
    | self=> exact hL
    | of_succ z hz IH=> exact v_paf F O v H he hn Hv M hf hz (IH (hf.trans (Nat.le_succ z)))
  exact H' l (before ..) le_rfl
end YM.PhysicalNext.InteractingRank.Soft
