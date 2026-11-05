import YM.Next.FLUCTUATIONS.Slots

/-!
# Both defects transported to another gauge

Use branch certificates, same choices k, constant-on-block extension
of the coarse gauge. Leave the operand w of D completely free. Pay
adjoints after real transport, allowing the slots and routes to wrap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {c f n : Side} {S : StepData c f}
open Work.E03

section paths
variable (z : Site n → G.El) (U : Config G n)
private lemma slot_at_gauge (x : Site n) (s : Slot) :
    s.atSite (gauge z U) x = G.adjoint (z x) (s.atSite U x) := by
  let p := Work.F03.slotFace s x
  have he : stop x s.walk = p.1 := by
    unfold p Work.F03.slotFace Slot.offset; rw [wrap_stop_cover, map_zero, add_comm]
    nth_rw 1 [show x=x+0 by rw [add_zero]]; rw [stop_add_left]
  rw [Work.F03.atSite_path, Work.F03.atSite_path,travel_gauge, he,face_gauge,G.curvature_conjugate]
  rw [G.adjoint_mul,G.adjoint_mul,← G.adjoint_mul (z p.1)⁻¹ (z p.1), inv_mul_cancel, G.adjoint_one]

private lemma shorten_gauge {A : Clip} (P : PathData G) {σ C Λ : ℝ} (hP : P.Bounds A σ C Λ)
    (R d : ℕ) (x : Cell n) :
    shorten P R d (gauge z U) x = G.adjoint (z x.1) (shorten P R d U x) := by
  let F := (G.adjoint (z x.1)).toContinuousLinearMap
  change (∑' i, shortenTerm P R d (gauge z U) x i) = F (∑' i, _)
  rw [F.map_tsum (shorten_summable _ _ hP _ _ _)]
  apply tsum_congr
  intro i; unfold shortenTerm; split
  next hi => rw [PathData.ellTerms,PathData.ellTerms, map_smul,slot_at_gauge]; rfl
  next hi => rw [map_zero]

private lemma plotted_gauge (A : Clip) (P : PathData G) {σ C Λ} (hP : P.Bounds A σ C Λ)
    (R d : ℕ) (i : Twin n) :
    plotted P A R d (gauge z U) i = G.adjoint (z i.1.1) (plotted P A R d U i) := by
  unfold plotted; split
  next hi => exact shorten_gauge z U P hP R d i.1
  next hi => rw [shoot,shoot,face_gauge,G.curvature_conjugate,map_smul]
end paths

section kernels
variable {X Y : Type*}

def turnData (z : Site c → G.El) (p : X → Site c) (u : X → G.Color) := fun x => G.adjoint (z (p x)) (u x)

variable (z : Site c → G.El) (p : X → Site c) (q : Y → Site c)
private def Turned (F H : X → Y → Pay G) :=
  ∀ i j (v : G.Color), H i j (G.adjoint (z (q j)) v) = G.adjoint (z (p i)) (F i j v)

private lemma ad_inner (u : G.El) (x y : G.Color) :
    inner ℝ (G.adjoint u x) (G.adjoint u y) = inner ℝ x y := by
  let E : G.Color →ₗᵢ[ℝ] G.Color := { G.adjoint u with norm_map' := G.norm_adjoint u }
  exact E.inner_map_map x y

variable {z p q}

private lemma Turned.flip {F H : X → Y → Pay G} (ht : Turned z p q F H) (i : X) (j : Y) (v : G.Color) :
    (H i j).adjoint (G.adjoint (z (p i)) v) = G.adjoint (z (q j)) ((F i j).adjoint v) := by
  apply ext_inner_left ℝ
  intro w
  suffices he : ∀ w' : G.Color, inner ℝ (G.adjoint (z (q j)) w') ((H i j).adjoint (G.adjoint (z (p i)) v)) =
      inner ℝ (G.adjoint (z (q j)) w') (G.adjoint (z (q j)) ((F i j).adjoint v)) by
    have h := he (G.adjoint (z (q j))⁻¹ w)
    rwa [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one] at h
  intro w'
  rw [ad_inner,ContinuousLinearMap.adjoint_inner_right,ht i j,ad_inner,
    ContinuousLinearMap.adjoint_inner_right]

private lemma Turned.roll_zip {F H : X → Y → Pay G} [Fintype Y] (ht : Turned z p q F H) (v : Y → G.Color) :
    zip H (turnData z q v) = turnData z p (zip F v) := by
  funext i
  simp only [zip,turnData, ht i,map_sum]

private lemma Turned.roll_unzip {F H : X → Y → Pay G} [Fintype X] (ht : Turned z p q F H) (v : X → G.Color) :
    unzip H (turnData z p v) = turnData z q (unzip F v) := by
  funext i
  simp only [unzip,turnData, ht.flip,map_sum]

variable (z)

private lemma turn_rated (U : Config G c) (y : Site c) (w : Walk) (a : ℝ) (v : G.Color) :
    rated (gauge z U) y w a (G.adjoint (z (stop y w)) v) = G.adjoint (z y) (rated U y w a v) := by
  change a • G.adjoint (travel (gauge z U) y w) _ = G.adjoint (z y) (a • G.adjoint _ _)
  rw [travel_gauge,map_smul,G.adjoint_mul,G.adjoint_mul,← G.adjoint_mul (z (stop y w))⁻¹ _,inv_mul_cancel,
    G.adjoint_one]

private lemma turn_summed (u v : G.El) (f h : Cover → Pay G)
    (hf : Summable f) (hh : Summable h)
    (he : ∀ z x, h z (G.adjoint u x) = G.adjoint v (f z x)) (x : G.Color) :
    (∑' z, h z) (G.adjoint u x) = G.adjoint v ((∑' z, f z) x) := by
  let Q := ContinuousLinearMap.apply ℝ G.Color (G.adjoint u x)
  let E := (G.adjoint v).toContinuousLinearMap.comp (ContinuousLinearMap.apply ℝ G.Color x)
  change Q (∑' z, h z) = E (∑' z, f z)
  rw [Q.map_tsum hh,E.map_tsum hf]
  exact tsum_congr fun z => he z x

private lemma turn_lane {α β : Type*} (K : Row α β) (hv : K.safe) (d R : ℕ)
    (V : Config G c) (a : X → Co c α) (b : Y → Co c β) :
    Turned z (Prod.fst ∘ a) (Prod.fst ∘ b) (fun i j => lane R d V K (a i) (b j))
      (fun i j => lane R d (gauge z V) K (a i) (b j)) := by
  intro i j x
  have hm (W : Config G c) : Summable (priced R d W K (a i) (b j)) := by
    apply Summable.of_norm_bounded (hv (a i).2 (b j).2)
    intro u; unfold priced; split
    next h => exact norm_rated_le ..
    next h => simp
  refine turn_summed _ _ _ _ (hm V) (hm (gauge z V)) ?_ x
  intro u x; unfold priced; split
  next h =>
    have he : stop (a i).1 (route 0 u 1) = (b j).1 := by
      rw [h.2]; simpa only [map_zero,add_zero] using Work.E03.stop_route (a i).1 0 u
    have hv := turn_rated z V (a i).1 (route 0 u 1) (K (a i).2 (b j).2 u) x
    rw [he] at hv; exact hv
  next h => simp

private lemma turn_leap (T : Tube G S) (hv : T.R.mf.safe) (R : ℕ) (V : Config G c) :
    Turned z (fun i => S.ratio.parent (mesh i).1) (fun j => (mesh j).1) (T.Φ R V) (T.Φ R (gauge z V)) := by
  intro i j x
  let w := (mesh i).1
  let g := S.ratio
  have hm (W : Config G c) : Summable (casted S T.R R W (mesh i) (mesh j)) := by
    apply Summable.of_norm_bounded (hv (g.residue w,(mesh i).2) (mesh j).2)
    intro u; dsimp only [casted]; split
    next h => exact norm_rated_le ..
    next h => simp
  refine turn_summed _ _ _ _ (hm V) (hm (gauge z V)) ?_ x
  intro u y; dsimp only [casted]; split
  next h =>
    let a := route (lift (g.residue w)) (S.patch.L.val • u) 1
    have he : g.parent (stop w a) = (mesh j).1 := by
      rw [show stop _ a=_ from casted_endpoint S w u,g.embed_parent]; exact h.2.symm
    rw [← copied S.ratio S.patch.odd_side]
    have ht := turn_rated (constantGauge z g) (replica g V) w a (T.R.mf (g.residue w,(mesh i).2) (mesh j).2 u) y
    simpa only [constantGauge, Function.comp_apply,he] using! ht
  next h => simp
end kernels

private lemma pred_gauge (hS : S.patch.Branches S.kernel G) (U : Config G f) (z : Site c → G.El)
    (k : S.Choices) : S.prediction (gauge (z ∘ S.ratio.parent) U) k = gauge z (S.prediction U k) := by
  funext e
  rw [StepData.prediction,S.updateGauged hS,(S.patch.bond_gauge (h:=hS) ..).2]
  simp only [Function.comp_apply,Ratio.embed_parent]; rfl

lemma gauge_gaps (P : Teller G) (T : Tube G S) (hP : P.Funds S T)
    (R : ℕ) (U : Config G f) (V : Config G c) (k : S.Choices)
    (z : Site c → G.El) :
    let U' := gauge (z∘S.ratio.parent) U; let V' := gauge z V
    ∀ i : Twin c, lGap T R U' (S.prediction U' k) V' i =
      G.adjoint (z i.1.1) (lGap T R U (S.prediction U k) V i) ∧
      ∀ w, dGap T R V' (turnData z (fun i : Twin c => i.1.1) w) i =
        G.adjoint (z i.1.1) (dGap T R V w i) := by
  intro U' V' i
  let p (i : Twin c) := i.1.1
  let q (i : Twin f) := S.ratio.parent i.1.1
  obtain ⟨h1,h2,h3,-⟩ := hP.crosses
  have hm : Turned z q p (T.Φ R V) (T.Φ R V') := turn_leap z T (Row.rights _ _ h3 P.width.le) R V
  have hn : Turned z Prod.fst p (T.Φ' R V) (T.Φ' R V') := turn_lane z T.R.mn (Row.rights _ _ h1 P.width.le)
    S.patch.L.val R V pole mesh
  have ho : Turned z Prod.fst p (T.N R V) (T.N R V') := turn_lane z T.R.o (Row.rights _ _ h2 P.width.le)
    S.patch.L.val R V id mesh
  obtain ⟨Λ,Λ',hX,hY⟩ := hP.feeds
  rw [← hP.high] at hX
  rw [← hP.low] at hY
  have hU : T.Xf R U' = turnData z q (T.Xf R U) := funext fun i =>
    plotted_gauge (z ∘ S.ratio.parent) _ _ _ hX _ _ i
  have hV : T.Xn R V' = turnData z p (T.Xn R V) := funext fun i => plotted_gauge z _ _ _ hY _ _ i
  have hZ : Z S (S.prediction U' k) V' = turnData z Prod.fst (Z S (S.prediction U k) V) := by
    have hh : S.patch.Branches S.kernel G := hP.knobs.symm ▸ hP.kernel
    unfold U' V'; rw [pred_gauge hh]
    funext i; unfold Z turnData Lattice.gauge
    rw [show z i.1 * V i * _ * (z i.1 * _ * _)⁻¹ = z i.1 * (V i * (S.prediction U k i)⁻¹) *
      (z i.1)⁻¹ by group,G.curvature_conjugate,map_smul]
  constructor
  · unfold lGap
    rw [hU,hV,hZ,hm.roll_unzip,hn.roll_unzip,map_sub,map_add]; rfl
  intro w
  unfold dGap; change turnData z p w i - _ = _
  rw [hm.roll_zip,hn.roll_zip,ho.roll_zip,hm.roll_unzip,hn.roll_unzip,ho.roll_unzip,map_sub,map_add,map_add]; rfl
end YM.Next.Fluctuations
