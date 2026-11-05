import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Incident
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.SmallLog
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Transport

/-!
# Stroke accuracy on protected stencils

Same U,V,Q at the F/I rows. Use real chart price on the tilted orientation;
not a formal expansion. The V argument agrees (beyond the row's stencil)
with an arbitrary small logarithmic lift. Don't require global body
controls when even that lift is after a change of gauge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations Work.E03
open Bloch Laurent
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {L : Side} {c f n : Side} {S : StepData c f} {T : Tube G S}

def baseStroke (T : Tube G S) (x : ℝ) (k : S.Choices) (V : Config G c) :=
    entryCost T (till x) (replica S.ratio V) k V

/-- Actual log agreement at touched bonds, AND magnitude bounds. -/
structure Grafted (V : Config G c) (U : Config G f) (u : Directions G f)
    (o : Site c) (B : ℕ) (h : ℝ) (S : StepData c f) : Prop where
  read : AgreeNear S.ratio.parent o B U (increment (replica S.ratio V) u)
  norm i : distAt S i o ≤ B → ‖u i‖ ≤ h

lemma replica_near {o : Site c} {V W : Config G c} {B} (h : AgreeNear id o B V W) :
    AgreeNear S.ratio.parent o B (replica S.ratio V) (replica S.ratio W) := fun i he => by
  unfold replica; split
  · rfl
  exact h _ he

lemma Grafted.spin {V U u o B h} (hg : Grafted (G := G) V U u o B h S) (z : Site c → G.El) :
    Grafted (gauge z V) (gauge (constantGauge z S.ratio) U) (spinRow S z u) o B h S := by
  constructor
  · intro i hi
    let t := constantGauge z S.ratio
    change t _ * U i*_=_
    rw [hg.read i hi, ← copied S.ratio S.patch.odd_side]
    unfold increment spinRow; rw [exp_adjoint]
    change t i.1*_*(t (i.1+step i.2))⁻¹=t i.1*_*(t i.1)⁻¹*(t i.1*_*_); unfold t; group
  intro i hi; rw [spinRow,G.norm_adjoint]; exact hg.norm _ hi

lemma Grafted.in_channel (s : Signed) {V U u} {o : Site c} {B h} (p : Grafted (G:=G) V U u (s.act o) (B+1) h S) :
    Grafted (pull s 0 V) (pull s 0 U) (displacement s u (replica S.ratio V)) o B h S := by
  constructor
  · intro i hi
    rw [← pulls_replica,← pull_increment,charge,charge,p.read _ (show distAt S _ _ ≤ _ from
      (projects S s o i).trans (Nat.add_le_add_right hi 1))]
  intro i hi; rw [size_displacement]; exact p.norm _ ((projects S s o i).trans (Nat.add_le_add_right hi 1))

lemma Grafted.less {V U u o i B d h} (p : Grafted (G:=G) V U u o B h S) (he : separation o i+d≤B) :
    Grafted V U u i d h S :=
  ⟨p.read.shrink he,fun v hv => p.norm v ((separation_triangle o i _).trans ((Nat.add_le_add_left hv _).trans he))⟩

lemma Grafted.raise {V U u o B h r} (p : Grafted (G:=G) V U u o B h S) (he : h ≤ r) :
    Grafted V U u o B r S := ⟨p.read,fun i hi => (p.norm i hi).trans he⟩

/-- In a crucial V hull where we know the *reference*. -/
theorem within (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G)
    {H : ℝ → ℝ} (h : Rate G L (-(1/2)) H) (hp : ∀ᶠ x in atTop, 0 ≤ H x) :
    ∃ M E : ℝ → ℝ, Rate G L (-(1/2)) M ∧ Rate G L (-1) E ∧
    ∀ᶠ x : ℝ in atTop, 0 ≤ M x ∧ 0 ≤ E x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch=D → Room P S T x → ∀ (b : LogField G c) (V : Config G c) (U : Config G f) (u : Directions G f)
        (k : S.Choices) (p : Rod c f), ‖b‖ ≤ H x →
      let d := radiusB x/4; let i := focus S p; let R := till x
      AgreeNear id i d V (represent b) → Grafted V U u i d (H x) S →
        let C := entryCost T R U k V p; let Y := baseStroke T x k V p
        let a := linearCopy S.ratio (collect G b)
        ‖C‖ ≤ M x ∧ ‖C - (Y + straightened T R V u p)‖ ≤ E x ∧
          ‖Y - linearCost T (toLog a) b p‖ ≤ E x := by
  obtain ⟨J,r,hJ,hr,hb⟩ := chart_bias G
  obtain ⟨B,hB,hX⟩ := bounded_stencils P D hd
  obtain ⟨A,t,hA,ht,hC⟩ := chord_chart_cost G
  let U x := H x*(1+J)
  have hp' : ∀ᶠ x in atTop,0 ≤ U x := hp.mono (fun x hx => by unfold U; positivity)
  obtain ⟨M,E,hM,hE,Hh⟩ := entry_near P L hd (show Rate G L (-(1/2)) U from h.mul_right _) hp'
  let q₁ x := B*(J*H x^2)
  let q₂ x := B*H x*Real.exp (-P.top.width*till x)
  let q₃ x := B*(2*G.colorScale*((radiusB x:ℝ)*(A*H x))*H x)
  have hv : Rate G L (-1) (fun x => (2*E x)+q₁ x+q₂ x+q₃ x) := by
    have h₁ : Rate G L (-1) q₁ := by convert (((h.pow 2).mul_left J).mul_left B) using 1; norm_num
    have h₂ : Rate G L (-1) q₂ := by
      convert ((h.mul_left B).mul (Rate.cutoff (a:=-(1/2:ℝ)) P.top.width_pos)) using 1; norm_num
    have h₃ : Rate G L (-1) q₃ := by
      convert (((((Rate.radius_price.mul (h.mul_left A)).mul_left (2*G.colorScale)).mul h).mul_left B)) using 1; norm_num
    exact (((hE.mul_left 2).add h₁).add h₂).add h₃
  refine ⟨_,_,hM.add (hE.weaken (by norm_num)),hv,?_⟩
  filter_upwards [Hh,hp,h.below (by norm_num) (min r t) (lt_min hr ht)] with x hx hp he
  obtain ⟨hl,hg,h⟩ := hx
  let X := H x
  obtain ⟨ha,he⟩ := le_min_iff.mp ((le_abs_self _).trans he)
  have hi : X ≤ U x := le_mul_of_one_le_right hp (le_add_of_nonneg_right hJ.le)
  have hf1 : 0 ≤ q₁ x := by unfold q₁; positivity
  have hf2 : 0 ≤ q₂ x := by unfold q₂; positivity
  have hf3 : 0 ≤ q₃ x := by unfold q₃; have := G.colorScale_pos; positivity
  refine ⟨add_nonneg hl hg,(by linarith),?_⟩
  intro c f S T hS hP b V U₀ u k p hk d i R hV hU C' Y a
  let v : Directions G f := fun j => if distAt S j i ≤ d then u j else 0
  have hw j (hj : distAt S j i ≤ d) : u j=v j := Eq.symm (if_pos hj)
  have hz : ‖v‖ ≤ X := (pi_norm_le_iff_of_nonneg hp).2 fun i => by
    dsimp only [v]; split
    next hi => exact hU.norm _ hi
    next hi => rwa [norm_zero]
  have hv : ‖a‖ ≤ X := (cp_cap S b).trans hk
  obtain ⟨w,hX',hc,hd'⟩ := hb v _ X hz hv ha
  have hq : ‖w‖ ≤ U x := hd'.trans (by unfold X U; nlinarith)
  have hpV := h c f S T hS hP.accepted (toLog w) b k (by rw [counted]; exact hq) (hk.trans hi) p
  have ht := h c f S T hS hP.accepted (toLog a) b k (by rw [counted]; exact hv.trans hi) (hk.trans hi) p
  have hU' : C'=entryCost T R (represent (toLog w)) k (represent b) p := by
    refine entry_stencil hP _ _ _ _ _ _ ?_ hV
    rw [← hX', exp_copy]
    intro j hj
    rw [hU.read _ hj]; unfold increment
    rw [hw j hj, replica_near hV j hj]
  have hf : Y=entryCost T R (represent (toLog a)) k (represent b) p := by
    have heq : represent (toLog a) = replica S.ratio (represent b) := by rw [represent,collects]; exact exp_copy S.ratio b
    rw [heq]; exact entry_stencil hP _ _ _ _ _ _ (replica_near hV) hV
  have hvs (j : Bond c) (hj : separation i j.1 ≤ d) : G.chord (V j)≤ A*H x := by
    have hh : ‖b (pole j)‖ ≤ X := le_trans (norm_le_pi_norm _ _) hk
    rw [hV j hj,Work.F03.represent_link]
    exact (hC _ (hh.trans he)).trans (mul_le_mul_of_nonneg_left hh hA.le)
  have hr := hP.frame
  have hn : 4*(R+predReach S.patch+4) ≤ d := by unfold d R till; omega
  have hy := hX c f S T hS hP.accepted
  have hR : ‖straightened T R V u p-barField T R v p‖ ≤ q₃ x := by
    have heq : straightened T R V u p=straightened T R V v p := by
      apply short_near T (SectorMeasure.funds_branch hP.accepted) _ _ _ _ _ p d hn (fun i _ => rfl)
      exact fun j hj => hw j (by unfold i; omega)
    rw [heq]
    refine (near_base hP.accepted hB hy V p R d v hn hp (mul_nonneg hA.le hp) hvs
      (fun j _ => le_trans (norm_le_pi_norm _ _) hz)).trans ?_
    unfold q₃
    have hc := G.colorScale_pos; gcongr; exact Nat.div_le_self _ _
  have hj : uncutField T (w-(v+a)) p+(uncutField T v p + linearCost T (toLog a) b p)=linearCost T (toLog w) b p := by
    rw [← linear_add T hP.accepted, ← linear_add T hP.accepted, sub_add_cancel]
  have hY : ‖uncutField T (w-(v+a)) p‖ ≤ q₁ x := (hy.full ..).trans
    (mul_le_mul_of_nonneg_left hc hB.le)
  have hf : ‖Y-linearCost T (toLog a) b p‖ ≤ E x := hf.symm ▸ ht.2
  have h' : ‖C'-linearCost T (toLog w) b p‖ ≤ E x := hU'.symm ▸ hpV.2
  have h'' : ‖uncutField T v p-barField T R v p‖ ≤ q₂ x := (hy.tail ..).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hB.le) (Real.exp_pos _).le)
  let z := linearCost T (toLog w) b p
  let z' := linearCost T (toLog a) b p
  have h'₂ : ‖C'‖ ≤ E x + M x := by
    exact (show ‖C'‖ ≤ ‖C'-z‖ + ‖z‖ by simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub C' z 0).trans
      (add_le_add h' hpV.1)
  refine ⟨by linarith only [h'₂],?_,hf.trans (by linarith)⟩
  let D := straightened T R V u p
  calc
    ‖C'-(Y+D)‖ = ‖(C'-z)+uncutField T (w-(v+a)) p +(z'-Y)+(uncutField T v p-barField T R v p)+(barField T R v p-D)‖ := by
      unfold z z'; rw [← hj]; abel_nf
    _ ≤ (((E x + q₁ x)+E x)+q₂ x)+q₃ x := by
      have he₁ := (norm_add_le (C'-z) (uncutField T (w-(v+a)) p)).trans (add_le_add h' hY)
      have hf : ‖z'-Y‖ ≤ E x := (norm_sub_rev z' Y).trans_le hf
      have hH : ‖barField T R v p-D‖ ≤ q₃ x := (norm_sub_rev ..).trans_le hR
      exact le_trans (norm_add_le ..) (add_le_add ((norm_add_le ..).trans (add_le_add
        ((norm_add_le ..).trans (add_le_add he₁ hf)) h'')) hH)
    _ = _ := by ring
end YM.ConnectedActivityE6.SliceRows
