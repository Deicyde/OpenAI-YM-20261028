import YM.Next.UV_STRESS.Dimension

/-!
# Normalization on one curve (not a new cutoff extraction)

The positive xi may be arbitrarily small. We use the *full* inverse
coordinates including scalars so boundedness is automatic; physical centering
is known independently of those bounds and then forces limit centering.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Table Ward Climb Extraction
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {V : DiffPlan (Bel C.book)} {W : DiffPlan S}

/-- Reindex only the comparison parameter, also allowing change of the
positive normalization. -/
def narrow (X : Scaling S) (p : Sequence) (w : ℕ → ℝ) (hw : ∀ k,0 < w k) : Scaling S :=
    ⟨fun k => X.U (p k), w, X.r ∘ p, hw, fun k => X.positive (p k), X.later.comp_strictMono p.monotone, X.drips.comp p.cofinal⟩

lemma narrow_path (X : Scaling S) (p : Sequence) (w : ℕ → ℝ) (hw : ∀ k,0 < w k)
    (H : Approaches (path X) (isoPanel X)) : Approaches (path (narrow X p w hw)) (isoPanel (narrow X p w hw)) where
  values n v :=
    { smooth := fun k => (H.values n v).smooth (p k)
      reads := fun s hs ht M he ε hh => p.cofinal.eventually ((H.values n v).reads s hs ht M he ε hh) }
lemma narrow_stable (X : Scaling S) (p : Sequence) (w : ℕ → ℝ) (hw : ∀ k,0 < w k)
    {H a} (ht : Stable H a W V X) : Stable H a W V (narrow X p w hw) :=
  ⟨fun d => p.cofinal.eventually (ht.hsym d), fun d e u => p.cofinal.eventually (ht.rises d e u),
    fun d => p.cofinal.eventually (ht.units d)⟩

def labelScale (X : Scaling S) (k : ℕ) (J : S.Stress) := transformed (X.U k 4).symm (X.r k ^ 4 • J)

def strength (X : Scaling S) (k : ℕ) (J : S.Stress) (T : (Bel C.book).Stress) : ℝ := ‖labelScale X k J‖ / ‖T‖

lemma positive_strength (X : Scaling S) (k : ℕ) {J : S.Stress} {T : (Bel C.book).Stress} (hp : J ≠ 0) (hT : T≠0) :
    0 < strength X k J T := by
  refine div_pos (norm_pos_iff.mpr (fun e => ?_)) (norm_pos_iff.mpr hT)
  apply (smul_ne_zero (pow_ne_zero 4 (X.positive k).ne') hp)
  funext i j
  apply (X.U k 4).symm.injective
  exact (congr_fun (congr_fun (show labelScale _ _ _=0 from e) i) j).trans (map_zero _).symm

def balanced_J (X : Scaling S) (J : S.Stress) (k : ℕ) : (Bel C.book).Stress := (X.xi k)⁻¹ • labelScale X k J

lemma balanced_value (X : Scaling S) (J : S.Stress) (k : ℕ) (i j : Axis) :
    X.U k 4 (balanced_J X J k i j) = ((↑((X.xi k)⁻¹ * X.r k^4):ℂ) • J i j) := by
  change X.U k 4 ((X.xi k)⁻¹ • ((X.U k 4).symm (X.r k^4 • J i j))) = _
  simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,LinearEquiv.apply_symm_apply, smul_smul]
  rw [Complex.ofReal_mul]; rfl

lemma subsector (X : Scaling S) (J : S.Stress) (L : (Bel C.book).Stress) (hJ : J≠0) (hL : L≠0) :
    ∃ p : Sequence, ∃ B : (Bel C.book).Stress, ‖B‖=‖L‖ ∧
      let Y := narrow X p
        (fun k => strength X (p k) J L) (fun k => positive_strength X (p k) hJ hL)
      Tendsto (balanced_J Y J) atTop (𝓝 B) := by
  let Y := narrow X Sequence.full (fun k => strength X k J L) (fun k => positive_strength _ _ hJ hL)
  have ht (k : ℕ) : balanced_J Y J k ∈ Metric.sphere 0 ‖L‖ := by
    rw [Metric.mem_sphere,dist_zero_right,balanced_J,norm_smul]
    change ‖(strength X k J L)⁻¹‖ * ‖labelScale X k J‖=‖L‖
    rw [Real.norm_of_nonneg (inv_pos.mpr (positive_strength _ _ hJ hL)).le]
    have hp := positive_strength X k hJ hL; unfold strength at *
    have hx : ‖labelScale X k J‖ ≠ 0 := fun h => by rw [h,zero_div] at hp; exact lt_irrefl _ hp
    field_simp
  obtain ⟨B,hb,p,hp,h⟩ := (isCompact_sphere ..).tendsto_subseq ht
  rw [Metric.mem_sphere,dist_zero_right] at hb
  exact ⟨⟨p,hp⟩, B,hb,h⟩

lemma balanced_zero (X : Scaling S) (H : S.Hierarchy) (B : KernelSpace H.spin) (ho : W.Orientation H.spin)
    (hb : currentDiv W H.spin ho B=0) (k i) : ∑ j : Axis, tiltScale X W k 4 j (balanced_J X B k j i)=0 := by
  have he (j : Axis) : tiltScale X W k 4 j (balanced_J X B k j i)=
      ((↑(X.r k * ((X.xi k)⁻¹*X.r k^4)):ℂ)) • (X.U k 5).symm (W.deriv 4 j (B.val j i)) := by
    let A := X.carry k (leaves W.deriv 4 j)
    let y := balanced_J X B k j i
    have hp : A y=(X.U k 5).symm (W.deriv 4 j (X.U k 4 y)) := rfl
    change X.r k • A y=_
    rw [hp]; unfold y; rw [balanced_value,map_smul,map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]
    exact congr_arg (fun s : ℂ => s • _) (Complex.ofReal_mul ..).symm
  simp_rw [he]; rw [← Finset.smul_sum,← map_sum,((linear_cons W _ ho _).1 hb).divergence i,map_zero,smul_zero]

lemma onepoint {L : Register G} (S : Table L) (v : S.Field 4) :
    expectation S 4 v = disc (fun _ : Fin 1 => (⟨4,v⟩ : S.Tag)) 0 := by
  have he : Fin.cons (α:=fun _ => S.Tag) ⟨4,v⟩ (blank S) = fun _ => ⟨4,v⟩ := by
    funext i; refine Fin.cases ?_ (fun j => Fin.elim0 j) i; rfl
  rw [expectation,Work.A01.front_eval,he]; rfl

lemma center_expect (H : S.Hierarchy) (hw : W.Derivatives S) (a : (Bel C.book).Hierarchy) (hV : V.Derivatives (Bel C.book))
    (X : Scaling S) (hp : Approaches (path X) (isoPanel X)) (v : ℕ → (Bel C.book).Field 4) (B : (Bel C.book).Field 4)
    (hb : Tendsto v atTop (𝓝 B)) :
    Tendsto (fun k => expectation S 4 (X.U k 4 (v k))) atTop (𝓝 (expectation (Bel C.book) 4 B)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  filter_upwards [travels_jet H hw a hV X hp (t:=fun _ : Fin 1 => 4) (fun k _ => v k)
    (fun _ => B) (fun _ => hb) 0 {0} isCompact_singleton (singleton_subset_iff.mpr conf1) _ (half_pos he)] with k hk
  rw [onepoint,onepoint,dist_eq_norm]
  specialize hk 0 rfl
  refine (le_trans (le_of_eq ?_) hk).trans_lt (half_lt_self he)
  let F : Points 1 → ℂ := tested (X.r k) (isoPanel X k) (fun _ : Fin 1 => (⟨4,v k⟩ : (Bel C.book).Tag))
  let T : Points 1 → ℂ := disc (fun _ : Fin 1 => (⟨4,B⟩ : (Bel C.book).Tag))
  change _= ‖iteratedFDeriv ℝ 0 F 0-iteratedFDeriv ℝ 0 T 0‖
  rw [show iteratedFDeriv ℝ 0 F 0-iteratedFDeriv ℝ 0 T 0 = iteratedFDeriv ℝ 0 (F-T) 0 by ext1 y; simp,
    norm_iteratedFDeriv_zero, Pi.sub_apply]; unfold F tested; rw [smul_zero]
  rfl

lemma on_axis (X : Scaling S) (H : S.Hierarchy) (hW : W.Derivatives S) (ho : W.Orientation H.spin) (B : KernelSpace H.spin)
    (hb : currentDiv W H.spin ho B=0) (a : (Bel C.book).Hierarchy) (hV : V.Derivatives (Bel C.book))
    (ht : V.Orientation a.spin) (hp : Approaches (path X) (isoPanel X)) (h : Stable H.spin a.spin W V X)
    (D : (Bel C.book).Stress) (hv : Tendsto (balanced_J X B) atTop (𝓝 D)) :
    ∃ w : KernelSpace a.spin, w.val=D ∧ currentDiv V a.spin ht w=0 := by
  have hu : D∈SymSpace a.spin := (Submodule.closed_of_finiteDimensional _).mem_of_tendsto hv
    ((vector_coherence H a h).mono fun k hk => (SymSpace a.spin).smul_mem _
      (transformed_mem (flips hk) ((SymSpace H.spin).smul_mem _ (kernel_mem.mp B.property).1)))
  have he (i j : Axis) : Tendsto (fun k => balanced_J X B k i j) atTop (𝓝 (D i j)) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hv i) j
  have hJ (i j : Axis) : expectation (Bel C.book) 4 (D i j)=0 := by
    refine tendsto_nhds_unique_of_eventuallyEq (center_expect H hW a hV X hp _ _ (he i j)) tendsto_const_nhds ?_
    filter_upwards with k
    rw [balanced_value,map_smul,(kernel_mem.mp B.property).2,smul_zero]
  refine ⟨⟨D,kernel_mem.mpr ⟨hu,hJ⟩⟩,rfl,Subtype.ext (funext fun i => ?_)⟩
  change ∑ j, V.deriv 4 j (D j i)=0
  have hQ (j) := Dash.arcing (bend_limit H hW a hV X 4 j hp) (he j i)
  exact tendsto_nhds_unique_of_eventuallyEq (tendsto_finsetSum _ (fun j _ => hQ j)) tendsto_const_nhds
    (Eventually.of_forall (fun k => balanced_zero X H B ho hb k i))

/-- Construct one coherent sign of the centered stress for the entire
weak comparison. Return also the stronger coherence/normalization along
one curve. `T` fixed; no assumption that a change of J0 is allowed. -/
theorem produce_current (H : S.Hierarchy) (hW : W.Derivatives S) (ho : W.Orientation H.spin)
    (a : (Bel C.book).Hierarchy) (T : Lighthouse C.book) (hV : T.W.Derivatives (Bel C.book)) (p : T.W.Orientation a.spin)
    (hT : FreeDiv T a p) (X : Scaling S) (hp : Approaches (path X) (isoPanel X)) (h : Stable H.spin a.spin W T.W X) :
    ∃ J : KernelSpace H.spin,∃ Y : Scaling S,J.val ≠ 0 ∧ currentDiv W H.spin ho J=0 ∧
      Approaches (path Y) (isoPanel Y) ∧ Stable H.spin a.spin W T.W Y ∧ Y.meter J.val T.J := by
  have hm := (differential_rank H a ho T p hT hW hV X hp h).2
  haveI : Nontrivial (LinearMap.ker (currentDiv W H.spin ho)) :=
    Module.finrank_pos_iff.mp (hm ▸ zero_lt_one)
  obtain ⟨⟨B,hB⟩,hn⟩ := exists_ne (0 : LinearMap.ker (currentDiv W H.spin ho))
  have hx : B ≠ 0 := fun e => hn (Subtype.ext e)
  have ht : B.val ≠ 0 := fun e => hx (Subtype.ext e)
  obtain ⟨s,R,hr,Hr⟩ := subsector X B.val T.J ht hT.sign
  let Y := narrow X s _ (fun k => positive_strength X (s k) ht hT.sign)
  have hY := narrow_path X s _ (fun k => positive_strength X (s k) ht hT.sign) hp
  have hS := narrow_stable X s _ (fun k => positive_strength X (s k) ht hT.sign) h
  obtain ⟨v,hv,hF⟩ := on_axis Y H hW ho B hB a hV p hY hS R Hr
  let t : KernelSpace a.spin := ⟨T.J,hT.enters⟩
  let j : LinearMap.ker (currentDiv T.W a.spin p) := ⟨t, (linear_cons _ _ p t).2 hT.origin⟩
  have he : j ≠ 0 := fun e => hT.sign (congr_arg (fun (x : LinearMap.ker (currentDiv T.W a.spin p)) => x.val.val) e)
  obtain ⟨c,hc⟩ := (finrank_eq_one_iff_of_nonzero' j he).1 hT.one ⟨v,hF⟩
  have hc : c • T.J = R := (congr_arg (fun (x : LinearMap.ker (currentDiv T.W a.spin p)) => x.val.val) hc).trans hv
  have hz := congr_arg norm hc; rw [norm_smul,hr,Real.norm_eq_abs] at hz
  have hz : |c|=1 := mul_right_cancel₀ (norm_pos_iff.mpr hT.sign).ne' (hz.trans (one_mul _).symm)
  suffices ht : ∃ J : KernelSpace H.spin, J.val ≠ 0 ∧ currentDiv W H.spin ho J = 0 ∧
      Tendsto (balanced_J Y J.val) atTop (𝓝 T.J) by
    obtain ⟨J,hJ,hj,HX⟩ := ht; refine ⟨J,Y,hJ,hj,hY,hS,fun i j => ?_⟩
    refine (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp HX i) j).congr fun k => ?_
    apply (Y.U k 4).injective
    change Y.U k 4 (balanced_J Y J k i j) = Y.U k 4 ((Y.U k 4).symm _); rw [LinearEquiv.apply_symm_apply,balanced_value]
  change Tendsto (balanced_J Y B.val) atTop (𝓝 R) at Hr
  rcases le_total 0 c with hh|hh
  · rw [abs_of_nonneg hh] at hz; rw [hz,one_smul] at hc
    exact ⟨B,ht,hB,hc ▸ Hr⟩
  rw [abs_of_nonpos hh] at hz; rw [show c=-1 from neg_eq_iff_eq_neg.mp hz, neg_one_smul] at hc
  refine ⟨-B,neg_ne_zero.mpr ht,by rw [map_neg, show currentDiv _ _ _ B=0 from hB,neg_zero],?_⟩
  refine Tendsto.congr' ?_ (show Tendsto (fun k => -balanced_J Y B k) atTop (𝓝 T.J) from by
    convert Hr.neg using 1
    rw [← hc,neg_neg])
  exact Eventually.of_forall fun k => by change -balanced_J Y _ k = balanced_J Y (-B.val) k; simp [balanced_J,labelScale]

def after (k : ℕ) : Sequence := ⟨fun i => i+k, fun i j hij => by simp [hij]⟩
def afterScale (X : Scaling S) (k : ℕ) := narrow X (after k) (fun j => X.xi ((after k) j)) (fun j => X.sign ((after k) j))

/-- Produce the exact `Track` along these J fields by tails. -/
theorem focused_track (H : S.Hierarchy) (hW : W.Derivatives S) (a : (Bel C.book).Hierarchy) (T : Lighthouse C.book)
    (hV : T.W.Derivatives (Bel C.book)) (X : Scaling S) (hp : Approaches (path X) (isoPanel X)) (h : Stable H.spin a.spin W T.W X)
    (J : S.Stress) (hb : X.meter J T.J) (N d m : ℕ) (R : ℝ) (hR : 1≤R) :
    ∃ k,Track (afterScale X k) W T J H.spin a.spin N d m R := by
    classical
    let L := max d 4
    have he : ∀ᶠ k in atTop, (∀ i≤L,_root_.YM.Spin.realH H.spin a.spin (X.U k i) ∧ X.U k i ((Bel C.book).unit i)=S.unit i) ∧
        (∀ (i j : ℕ) (h : i ≤ j), j ≤ L → ∀ x, X.U k j (T.W.rise h x)= W.rise h (X.U k i x)) := by
      have hu := eventually_all.mpr (fun i : Fin (L+1) => (h.hsym i).and (h.units i))
      have hv : ∀ᶠ k in atTop,∀ i j : Fin (L+1), ∀ (h : i.val ≤ j.val), ∀ x, X.U k j (T.W.rise h x) = W.rise h (X.U k i x) :=
        eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun g => h.rises i j g
      filter_upwards [hu,hv] with k hk he
      exact ⟨fun i hi => hk ⟨i,Nat.lt_succ_of_le hi⟩, fun i j w hj => he ⟨i,Nat.lt_succ_of_le (w.trans hj)⟩ ⟨j,Nat.lt_succ_of_le hj⟩ w⟩
    obtain ⟨k,hk⟩ := eventually_atTop.mp he
    let p : Sequence := after k
    let Y := narrow X p (fun j => X.xi (p j)) (fun j => X.sign (p j))
    refine ⟨k,⟨?_,comparison_jets H hW a hV Y (narrow_path X p _ _ hp) N d m R (zero_lt_one.trans_le hR),
      fun i j => (hb i j).comp p.cofinal⟩⟩
    constructor
    · exact fun i j hj => (((hk _ (show k ≤ p i from Nat.le_add_left k i)).1 j hj).1)
    · exact fun i j hj => (((hk _ (show k ≤ p i from Nat.le_add_left k i)).1 j hj).2)
    exact fun i j l t w => (hk _ (show k ≤ p i from Nat.le_add_left k i)).2 j l t w

/-- Produce the exact `ActLaw` along these J fields by tails. -/
theorem focused (H : S.Hierarchy) (hW : W.Derivatives S) (a : (Bel C.book).Hierarchy) (T : Lighthouse C.book)
    (hV : T.W.Derivatives (Bel C.book)) (X : Scaling S) (hp : Approaches (path X) (isoPanel X)) (h : Stable H.spin a.spin W T.W X)
    (J : S.Stress) (hb : X.meter J T.J) : ActLaw W T J H.spin a.spin where
  connects N d m R hR := by
    obtain ⟨k,he⟩ := focused_track H hW a T hV X hp h J hb N d m R hR
    exact ⟨afterScale X k,he⟩
end YM.Next.UVStress
