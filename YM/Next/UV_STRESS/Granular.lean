import YM.Next.UV_STRESS.Glide

/-!
# The two-regime quantitative receipts imply the true Station estimates

Intensity costs per **finite basis** and power determined by arity. Lift
operators need not be contractions etc. No schedule sufficiency inferred.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Extraction Climb Ward Table Cells
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order}
variable {D N n : ℕ} {R : ℝ} {t : Caps n}

structure RA (W : ℕ → Wheel C D) (F : Extraction.Order) (H : (Bel C.book).RealSpin) : Prop where
  grants : ∀ᶠ k in atTop, ∃ A : ℝ, F.late fun N p => ‖(W k).atCut (N,p)‖ ≤ A
  central : ∀ᶠ k in atTop,F.late fun N p => (W k).atCut (N,p) (⟨0,Nat.succ_pos D⟩ : Fin (D+1)) ((Bel C.book).unit 0) = C.book.scalar 0
  real : ∀ᶠ k in atTop,F.late fun N p => ∀ (i : Fin (D+1)) v, (W k).atCut (N,p) i ((Bel C.book).conj H i v) = star ((W k).atCut (N,p) i v)
  h_symm : ∀ᶠ k in atTop,F.late fun N p => ∀ (i : Fin (D+1)) s v,
    (W k).atCut (N,p) i ((Bel C.book).mirror H i s v) = C.book.mirrorGroup i s ((W k).atCut (N,p) i v)

abbrev record (C : Family G) (t : Caps n) := Code fun i => (Bel C.book).Field (t i)

def depthWord (t : Caps n) (p : record C t) : Ribbon (Bel C.book) t := combination _ p

/-- One regime prices both size and interpolation. `Balances.on_`/`off` etc in Balances
apply *without* assuming any one local limit is already read for W. -/
structure Granular (W : ℕ → Wheel C D) (F : Extraction.Order) (H : (Bel C.book).RealSpin)
    (N : ℕ) (R : ℝ) : Prop extends RA W F H where
  small : Tendsto (fun k => (W k).r) atTop (𝓝 0)
  proof_ (n : ℕ) (hn : n ≤ N) (t : Caps n) (hu : ∀ i, t i≤D) (x : record C t) :
    ∃ e A B, Balances W F R hu (depthWord t x) e A B

lemma Granular.upon {W : ℕ → Wheel C D} {H} (h : Granular W F H N R) (f : Extraction.Order) :
    Granular W (F.refine f) H N R where
  small := h.small
  grants := h.grants.mono fun i hi => ⟨hi.choose, F.late_refine f hi.choose_spec⟩
  central := h.central.mono fun i hi => F.late_refine f hi
  real := h.real.mono fun i hi => F.late_refine f hi
  h_symm := h.h_symm.mono fun i hi => F.late_refine f hi
  proof_ n hn t hu x := by
    obtain ⟨e,A,B,hB⟩ := h.proof_ n hn t hu x; exact ⟨e,A,B,hB.upon W f⟩

private lemma bounded_code (t : Caps n) : ∃ A : ℝ,0<A ∧ ∀ w : Ribbon (Bel C.book) t,
    (∑ j : record C t, ‖coords _ j w‖) ≤ A * Station.charge (hang t w) := by
  let S (i) := (Bel C.book).Field (t i)
  let B (j : record C t) i := LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (S i)).coord (j i))
  let U (j : record C t) := ∏ i, ‖B j i‖
  refine ⟨(∑ j, U j)+1,add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => by unfold U; positivity)) zero_lt_one,fun w => ?_⟩
  have hs (j : record C t) : ‖coords _ j w‖ ≤ U j * Station.charge (hang t w) := by
    rw [coords,norm_prod,Station.charge]; unfold U
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => (B j i).le_opNorm (w i)
  apply le_trans (Finset.sum_le_sum (fun i _ => hs i))
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (by linarith) (show 0 ≤ ∏ i : Fin n, ‖w i‖ by positivity)

private lemma errors_total (W : Station C D) (hh : ∀ i,t i ≤ D) (hP : (Bel C.book).Smooth) (w : Ribbon (Bel C.book) t)
    (T : Test n) (N p : ℕ) : W.paid (hang t w) hh T N p- T.applyTo (disc (hang t w)) =
    ∑ j : record C t, coords _ j w * (W.paid (hang t (depthWord t j)) hh T N p - T.applyTo (disc (hang t (depthWord t j)))) := by
  let g j := depthWord (C:=C) t j
  let A (z : Ribbon (Bel C.book) t) := W.paid (hang t z) hh T N p
  let B (z : Ribbon (Bel C.book) t) := disc (hang t z)
  have ht : T.applyTo (B w)= ∑ j : record C t, coords _ j w * T.applyTo (B (g j)) := by
    have he' : B w = fun x => ∑ j : record C t, coords _ j w * B (g j) x :=
      funext fun x => basis_tuple _ _ ((Bel C.book).classMoment (Bel C.book) t x)
    rw [he']; unfold Test.applyTo; simp_rw [Finset.mul_sum]
    have hp (j : record C t) (x : Points n) : T x * (coords _ j w * B (g j) x)=coords _ j w * (T x * B (g j) x) := by ring
    simp_rw [hp,← integral_const_mul]; exact integral_finsetSum _ fun j _ =>
      (T.smearing (smoothDisc (T:=Bel C.book) hP (hang t (g j))).continuousOn).const_mul _
  let T' := dilate W.rad T
  let M := (((C.S.a N : ℂ)^(4*n)) • ∑ r : Fin n → Lattice.Site (C.side N p), T' (Order.cells C N p r) • C.ensemble t r).compLinearMap
    fun i => (W.atCut (N,p) ⟨t i,Nat.lt_succ_of_le (hh i)⟩).toLinearMap
  have he (x : Ribbon (Bel C.book) t) : A x = M x := by
    simp only [M, MultilinearMap.compLinearMap_apply, _root_.smul_apply,_root_.sum_apply, smul_eq_mul]
    rfl
  change A w-T.applyTo (B w)=∑ j : record C t, coords _ j w * (A (g j)-T.applyTo (B (g j)))
  simp_rw [mul_sub, Finset.sum_sub_distrib, ht,he]
  rw [basis_tuple _ w M]; rfl

section
variable {a : (Bel C.book).RealSpin}
variable (W : ℕ→ Wheel C D) (h : Granular W F a N R)
variable (hS : F.Ordered C S) (hs : S.Smooth) (hC : C.Makes) (ht : F.PointLimits C S) (hm : (Bel C.book).Smooth)
variable (hR : 0<R) (ε : ℝ) (he : 0<ε)
include h hS hs ht hC hm hR he

lemma pay_word (t : Caps n) (hn : n ≤ N) (hu : ∀ i, t i ≤ D) :
    ∀ᶠ k in atTop, ∀ w : Ribbon (Bel C.book) t, ∀ f : Test n, tsupport f ⊆ Scaling.window R n →
      ∀ M : ℝ,0<M → (∀ x, ‖f x‖ ≤ M) → F.upper
      (fun N p => ‖(W k).paid (hang t w) hu f N p - f.applyTo (disc (hang t w))‖) (ε*Station.charge (hang t w)*M) := by
  obtain ⟨A,hA,hB⟩ := bounded_code (C:=C) t
  have hp (j : record C t) : ∀ᶠ k in atTop, ∀ f : Test n, tsupport f ⊆ Scaling.window R n →
      ∀ M : ℝ, 0 < M → (∀ x, ‖f x‖ ≤ M) → F.upper
      (fun N p => ‖(W k).paid (hang t (depthWord t j)) hu f N p-f.applyTo (disc (hang t (depthWord t j)))‖) (M*(ε/A)) := by
    obtain ⟨e,a,b,he'⟩ := h.proof_ n hn t hu j; exact cutoff_balance W hC hR ht hs hm hu _ he' hS h.grants _ (by positivity)
  filter_upwards [eventually_all.mpr hp] with k hk w f hf M hM hv η hη
  let b (j : record C t) := coords _ j w
  let q (u : ℕ×ℕ) (v : Ribbon (Bel C.book) t) := (W k).paid (hang t v) hu f u.1 u.2 - f.applyTo (disc (hang t v))
  let r := Station.charge (hang t w)
  let P := ∑ j,‖b j‖
  have hP : 0≤P := by unfold P; positivity
  let δ := η/(1+P)
  have hd : 0 < δ := by unfold δ; positivity
  change ∀ᶠ i in F.fuse, ‖q i w‖ ≤ _
  have ht : ∀ᶠ i in F.fuse, ∀ j, ‖q i (depthWord t j)‖ ≤ M*(ε/A)+δ := eventually_all.mpr
    fun (j : record C t) => hk j f hf M hM hv _ hd
  filter_upwards [ht] with i hi
  have hh : P*δ ≤ η := le_trans (mul_le_mul_of_nonneg_right (by linarith) hd.le) (show (1+P)*δ ≤ η by
    unfold δ; rw [mul_div_cancel₀ _ (by linarith)])
  calc
    _ = ‖∑ j : record C t,b j * q i (depthWord t j)‖ := congr_arg norm (errors_total _ hu hm w ..)
    _ ≤ _ := (norm_sum_le ..).trans (by
      calc
        _ ≤ P*(M*(ε/A)+δ) := by
          unfold P; rw [Finset.sum_mul]; exact Finset.sum_le_sum (fun j _ => by rw [norm_mul]; gcongr; exact hi j)
        _ ≤ (A*r * (M*(ε/A))) + η := by rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_right (hB w) (by positivity)) hh
        _ = _ := by unfold r; field_simp)

/-- Pay at *all* t and w, genuinely uniform one station. -/
theorem supply_wheel : ∀ᶠ k in atTop, (W k).toStation.Admissible F a N R ε := by
  have hp (n : Fin (N+1)) (t : Fin n → Fin (D+1)) := pay_word W h hS hs hC ht hm hR ε he (fun i : Fin n => (t i).val)
    (Nat.le_of_lt_succ n.isLt) (fun i => Nat.le_of_lt_succ (t i).isLt)
  filter_upwards [h.grants,h.central,h.real,h.h_symm,eventually_all.mpr fun n => eventually_all.mpr (hp n)] with i hi hc hr hx hh
  refine ⟨hi,hc,hr,hx,fun {n} hu v hu' => ?_⟩
  let b : Fin (N+1) := ⟨n,Nat.lt_succ_of_le hu⟩
  let t (i : Fin n) : Fin (D+1) := ⟨(v i).1,Nat.lt_succ_of_le (hu' i)⟩
  exact hh b t (fun j => (v j).2)
end

/-- Real weak estimate production, conditional quantitative prices. Not
proving from Seed some assumed scheduling inequality for the Wilson beta path.
Call `foundation` with this. -/
theorem realizes_stations (hC : C.Makes) (ht : F.PointLimits C S) (hS : F.Ordered C S) (hs : S.Smooth)
    (hm : (Bel C.book).Smooth) (a : (Bel C.book).RealSpin)
    (estimate : ∀ (N D : ℕ) (R : ℝ), 1 ≤ R → ∃ W : ℕ → Wheel C D, Granular W F a N R) : Stations C F a where
  arbitrarily D N R ε δ hr he hd := by
    obtain ⟨W,hW⟩ := estimate N D R hr
    obtain ⟨k,hk,H⟩ := ((supply_wheel W hW hS hs hC ht hm (by linarith) ε he).and (hW.small.eventually (ge_mem_nhds hd))).exists
    exact ⟨(W k).toStation,hk,H⟩
end YM.Next.UVStress
