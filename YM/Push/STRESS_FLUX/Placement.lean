import YM.Next.BOUNDARY.Synchronize
import YM.Push.STRESS_FLUX.Matching
import YM.Push.STRESS_FLUX.Polynomial

/-! Placement and normalization helpers on the actual `Quotes` arrays.
For sufficiently shallow inserted fields, the full product gate follows
without new matching work (given the previous centered budgets). For general
fields proves interior fit of the *actual* comparison, not decay of its norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Matching
open Function Set Filter Wilson Lattice Extraction Cells Labels MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {n : Side} {D d k J m l N p h : ℕ} {f : Extraction.Order}

lemma through_margin (T : Tiling n) (ht : 0<k) (x : Cover) (hx : ∀ i, (x i).natAbs ≤ k) {z : Site n} {w : T.Cell} (hz : z∈T.margin w (2*k)) : wrap n x + z ∈ T.margin w k := by
  have hi i : k ≤ T.coordinated w (wrap n x + z) i ∧ T.coordinated w (wrap n x+z) i + k + T.kind.shift ≤ T.side.val := by
    obtain ⟨h1,h2⟩ := hz.2 i; have h3 := hx i
    let b : ℤ := T.coordinated w z i + x i
    have he : 0 < b := by unfold b; omega
    have hh : b.toNat < T.side.val := by unfold b; omega
    have hr : T.coordinated w (wrap n x + z) i = b.toNat := by
      rw [Tiling.coordinated, ← ZMod.val_natCast_of_lt (hh.trans T.narrow)]; apply congr_arg ZMod.val
      rw [← Int.cast_natCast, Int.toNat_of_nonneg he.le]; unfold b; push_cast
      change (x i:Per n)+z i - T.starts w i = _; simp [Tiling.coordinated,Per]; abel
    rw [hr]; unfold b at *; omega
  refine ⟨fun i => ?_,hi⟩
  have hh := hi i; change T.kind.Strict _ (T.coordinated _ _ _); cases T.kind <;> unfold Kind.Strict <;> omega

lemma small_offset {e : ℝ} (he : 0 ≤ e) (ht : e ≤ C.S.a k) (h : k ≤ N) {z : E4} (hz : ‖z‖ ≤ 1) (i : Axis) :
    ⌈(e • z) i / C.S.a N⌉.natAbs ≤ Cells.span C.S h p := by
  have hp := C.S.embeds_scale (C.S.toDepth h p); have hN := C.S.a_pos N
  have hi := (PiLp.norm_apply_le z i).trans hz; rw [Real.norm_eq_abs,abs_le] at hi
  have hb : e * z i ∈ Icc (-C.S.a k) (C.S.a k) := by constructor <;> nlinarith [hi.1,hi.2]
  rw [← hp] at hb
  have h1 : ⌈e*z i / C.S.a N⌉ ≤ (Cells.span C.S h p : ℕ) := Int.ceil_le.mpr ((div_le_iff₀ hN).2 (by push_cast; linarith [hb.2]))
  have h2 : -(((Cells.span C.S h p : ℕ) : ℤ)) ≤ ⌈e*z i / C.S.a N⌉ := by
    have hh : (-(((Cells.span C.S h p : ℕ):ℤ)):ℝ) ≤ (↑⌈e*z i / C.S.a N⌉:ℝ) := ((le_div_iff₀ hN).2 (by push_cast; linarith [hb.1])).trans (Int.le_ceil _)
    exact_mod_cast hh
  change ⌈e*z i / C.S.a N⌉.natAbs ≤ _; omega

structure SeatsAt (C : Family G) (v : C.book.Token) (N p m J : ℕ) (e A : ℝ) : Prop where
  late : m≤N
  sit (z : E4) (hz : ‖z‖ ≤ 1) (T : Tiling (C.side N p)) (hT : T.side.val = Cells.span C.S late p)
    (ho : (0 : Site (C.side N p)) ∈ T.margin 0 (T.side.val / (8*(J+1)))) :
    (∀ u : C.label v.1, Interior (T.chamber 0) (C.O N p (d:=v.1) u (ceilSite C N p (e • z)))) ∧ T.rootTest (C.beta N p) (C.seen v (ceilSite C N p (e • z))) ≤ A

theorem seats (H : C.Makes) (he : CenteredBook C f) (v : C.book.Token) (m J : ℕ) (e : ℕ → ℝ) (hp : ∀ k, 0 ≤ e k) (ht : Tendsto e atTop (𝓝 0)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ k in atTop, ∀ᶠ i : ℕ×ℕ in f.fuse, SeatsAt C v i.1 i.2 m J (e k) A := by
  obtain ⟨j,hm,hj,A,hA,hB⟩ := ((eventually_ge_atTop m).and ((width (C:=C) (2*J+1) m).and ((Around.image_ (fun _ : Fin 1 => v) he).2))).exists
  refine ⟨A,hA,?_⟩
  filter_upwards [ht.eventually (ge_mem_nhds (C.S.a_pos j))] with k hk
  filter_upwards [(show ∀ᶠ i in f.fuse, Around.imageBudget (fun _ : Fin 1 => v) A j i.1 i.2 from hB)] with i h
  refine ⟨hm.trans h.1, fun z hz T hT ho => ?_⟩
  let t := Cells.span C.S h.1 i.2
  have ht : 2*(3*t) ≤ T.side.val / (8*(J+1)) := by
    rw [hT,Nat.le_div_iff_mul_le (by omega), show 2*(3*t)*(8*(J+1))=3*t*(8*(2*J+1+1)) by ring]
    exact (Nat.le_div_iff_mul_le (by omega)).1 (hj (hm.trans h.1) h.1)
  have hmrg : ceilSite C i.1 i.2 (e k • z) ∈ T.margin 0 (3*t) := by
    rw [ceilSite,← add_zero (wrap _ _)]
    refine through_margin T (Nat.mul_pos (by decide) ((C.S.toDepth h.1 i.2).count.property)) _ (fun a => ?_) (Lease.fewer T 0 ht ho)
    exact (small_offset (hp k) hk h.1 hz _).trans (Nat.le_mul_of_pos_left _ (by decide))
  have hfit := (h.2 0 (1,false)).2
  dsimp only at hfit; rw [Extraction.Spin.choose_id] at hfit
  have hI y (hy : y ∈ T.margin 0 (2*t)) (u : C.label v.1) : Interior (T.chamber 0) (C.O i.1 i.2 (d:=v.1) u y) :=
    Around.figure H _ (⟨v.1,u⟩ : C.book.Token) _ y hy (fun z hz a => (hfit.choose_spec z hz a).trans_le (show t ≤ 2*t by omega))
  exact ⟨hI _ (Lease.fewer T 0 (by omega) hmrg), Around.interior_from T v H h.1 (hT ▸ Around.inherits hm h.1) A (fun b => (h.2 0 b).1) (fun _ hy => hI _ hy v.2) _ hmrg⟩



lemma test_scale_complex {T : Tiling n} {β : ℝ} (F : Config G n → ℂ) (c : ℂ) : T.rootTest β (fun U => c * F U) ≤ ‖c‖ * T.rootTest β F := by
  classical
  let z (v : T.Cell) := if T.hand v then star c else c
  have he (U : Config G n) : (∏ v : T.Cell, T.copy v (fun U => c * F U) U) = (∏ v, z v) * ∏ v, T.copy v F U := by
    rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro v _; by_cases h:T.hand v <;> simp [z,Tiling.copy,h,star_mul']
  have hh v : ‖z v‖ = ‖c‖ := by unfold z; split <;> simp
  apply le_of_pow_le_pow_left₀ T.cells_positive.ne' (mul_nonneg (norm_nonneg _) (T.root_nonneg ..))
  rw [mul_pow,T.powering,T.powering]
  change ‖∫ U, ∏ v : T.Cell, T.copy v (fun U => c*F U) U ∂law G n β‖ ≤ ‖c‖^_ * ‖∫ U, ∏ v : T.Cell, T.copy v F U ∂law G n β‖
  simp_rw [he,integral_const_mul, norm_mul, Complex.norm_prod, hh,Finset.prod_const, Finset.card_univ]
  exact le_rfl

private lemma affine_label {d : ℕ} (hd : d < 4) (p : Pol G) (he : p ∈ Labels.limited G d) :
    ∃ c : ℂ, ∃ l : Jet G →ₗ[ℝ] ℂ, ∀ J, Labels.read J p = c + l J := by
  rw [limited,MvPolynomial.restrictSupport_eq_span] at he
  induction he using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨M,hM,rfl⟩ := h
    rcases eq_or_ne M 0 with rfl|h0
    · exact ⟨1,0,fun J => by simp⟩
    obtain ⟨i,N,hN,h⟩ := peel_weight h0
    have he : N=0 := by
      by_contra he; obtain ⟨a,b,-,hb⟩ := peel_weight he; change height M ≤ d at hM; unfold generation at *; omega
    rw [he,add_zero] at hN
    refine ⟨0,Complex.ofRealAm.toLinearMap.comp (((axes G i.1).coord i.2).comp (LinearMap.proj i.1)),fun J => ?_⟩
    rw [hN,zero_add]; change MvPolynomial.aeval _ (MvPolynomial.X _) = _; rw [MvPolynomial.aeval_X]; rfl
  | zero => exact ⟨0,0,fun _ => by simp⟩
  | add p q _ _ hp hq => obtain ⟨c,l,h⟩ := hp; obtain ⟨b,x,g⟩ := hq; exact ⟨c+b,l+x,fun _ => by simp [h,g]; abel⟩
  | smul c p _ hp => obtain ⟨b,l,h⟩ := hp; exact ⟨c • b,c • l,fun _ => by simp [h,mul_add]⟩

theorem tiny (h : G.Simple) (hd : d < 4) (p : Label G d) : ∃ c : ℂ, p = c • Labels.unit G d := by
  obtain ⟨c,l,hp⟩ := affine_label hd p.val p.property.1
  let A := Low.mk c l (0 : Taylor G 0 →ₗ[ℝ] Taylor G 0 →ₗ[ℝ] ℂ) 0
  have he : l=0 := Low.linear_invariant h (A:=A) (Low.covariance (p:=p) (fun _ _ => rfl) (fun _ => by simp [hp,A,Low.eval]))
  refine ⟨c, label_ext (fun J => ?_)⟩
  rw [hp,he,LinearMap.zero_apply, add_zero]
  change _ = Labels.read J (c • 1)
  simp
lemma tiny_reference (h : G.Simple) (hd : d < 4) (B : C.label d) : ∃ c : ℂ, B = c • C.refUnit d := by
  let F := C.labels.level d
  obtain ⟨c,hc⟩ := tiny h hd (F.coords.symm B)
  let t := ((C.S.a (C.ref d):ℂ)^d)
  refine ⟨c/t,?_⟩; rw [← F.coords.apply_symm_apply B,hc, map_smul,F.coords_unit]; change _ = (c/t) • t • F.e0
  have ht : t ≠ 0 := by unfold t; exact_mod_cast pow_ne_zero d (C.S.a_pos (C.ref d)).ne'
  rw [smul_smul,div_mul_cancel₀ _ ht]

theorem quotes_tiny (hf : G.Simple) (H : C.Makes) (he : CenteredBook C f) (v : Rows C) (B : C.label d) (hd : d < 4) (hh : 0<h) : Quotes f v B D h := by
  obtain ⟨c,hc⟩ := tiny_reference hf hd B
  intro J m; refine ⟨m,le_rfl,fun l => ?_⟩
  choose A hA HA using fun a b : Axis => seats H he ⟨4,v a b⟩ m J C.S.a (fun k => (C.S.a_pos k).le) C.S.shrinks
  obtain ⟨P,hP⟩ := (eventually_all.mpr fun a => eventually_all.mpr fun b => eventually_ge_atTop (A a b)).exists
  refine ⟨max m l,le_rfl,C.S.a,fun k => (C.S.a k^h * ‖c‖) * P, fun k => ⟨C.S.a_pos _, mul_nonneg (mul_nonneg (pow_nonneg (C.S.a_pos _).le _) (norm_nonneg _)) ((hA 0 0).trans (hP _ _))⟩,C.S.shrinks,?_,?_⟩
  · simpa only [zero_pow hh.ne',zero_mul] using ((C.S.shrinks.pow h).mul_const ‖c‖).mul_const P
  have hi t : ∀ᶠ i : ℕ × ℕ in f.fuse, t ≤ i.1 := Eventually.of_forall (fun _ => f.mesh.cofinal.eventually (eventually_ge_atTop t)) (f:=atTop)
  filter_upwards [eventually_all.mpr fun a => eventually_all.mpr (HA a)] with k hk z _ hz a b
  refine ⟨0,?_⟩
  filter_upwards [hi (max m l), hi (C.ref d),hk a b] with i hl href ht
  let y := ceilSite C i.1 i.2 (C.S.a k • z)
  let F := C.O i.1 i.2 (d:=4) (v a b) y
  have hF : cluster (v a b) B (C.S.a k ^ h) y (0 : C.label D) = (fun U => ((C.S.a k:ℂ)^h * c) * F U) := by
    unfold cluster Family.seen F
    rw [hc, (C.linearO ..).map_smul, C.constant H d href,(C.linearO ..).map_zero]
    ext1 U
    simp [mul_comm,mul_assoc]
  refine ⟨0,by simp,ht.late,hl,fun T _ hT _ ho => ?_⟩
  obtain ⟨hy,hY⟩ := ht.sit z hz T hT ho
  rw [hF]
  have := C.S.a_pos k
  refine ⟨(hy _).scale _, (test_scale_complex ..).trans (mul_le_mul ?_ hY (T.root_nonneg ..) (by positivity) |>.trans (mul_le_mul_of_nonneg_left (hP a b) (by positivity)))⟩
  rw [norm_mul,Complex.norm_pow,Complex.norm_real, Real.norm_of_nonneg (C.S.a_pos _).le]
end YM.StressFlux.Matching
