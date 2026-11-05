import YM.Ward.Walk

/-!
# Geometry . Park to-axis from injective times any chosen
normal, three movements of the earliest, conceptually. Includes no path with
zero/invalid segment, though intervals can be degenerate. Perturb any Conf via
avoiding finitely many hyperplanes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ward
open Set Function Filter
open scoped Topology BigOperators
variable {n : ℕ} (a b : Axis)

abbrev arranged (x : Points n) := Injective (fun i : Fin n => x i a)
lemma also {x : Points n} (h : arranged a x) : x∈ conf n := fun _ _ e => h (congr_arg (fun p : E4 => p a) e)
lemma suffices_dist {x y : Points n} {j : Fin n} (h : x∈conf _) (he : ∀ i≠j, x i=y i)
    (hp : ∀ i≠j, y i a ≠ y j a) : y∈conf _ := by
  intro i k hg
  by_contra hk
  have hx : y i a=y k a := congr_arg (fun p : E4 => p a) hg
  by_cases p : j=i
  · subst i; exact hp k (Ne.symm hk) hx.symm
  by_cases s : j=k
  · subst k; exact hp _ hk hx
  exact hk ((show Injective x.ofLp from h) ((he i (Ne.symm p)).trans (hg.trans (he k (Ne.symm s)).symm)))

lemma still_first {x : Points n} {k : Fin n} (h : Earliest x a k) (w : b≠a) (s : ℝ) : Earliest (cast x k b s) a k := by
  have he (j) (hj : j≠k) : cast x k b s k a < cast x k b s j a := by simp [atCast,near x k j hj,w.symm,h.2 j hj]
  exact ⟨suffices_dist a h.1 (fun i hi => (near x k i hi b s).symm) (fun i hi => (he i hi).ne'),he⟩
lemma still_last {x : Points n} {k : Fin n} (h : Latest x a k) (w : b≠a) (s : ℝ) : Latest (cast x k b s) a k := by
  have he (j) (hj : j≠k) : cast x k b s j a < cast x k b s k a := by simp [atCast,near x k j hj,w.symm,h.2 j hj]
  exact ⟨suffices_dist a h.1 (fun i hi => (near x k i hi b s).symm) (fun i hi => (he i hi).ne),he⟩

lemma park1 {x : Points n} {k : Fin n} (h : Latest x a k) : ∀ s : Finset Axis,
    a∉s → ∃ y : Points n, Walk n x y ∧ y k a=x k a ∧ (∀ i≠k, x i=y i) ∧
      Latest y a k ∧ ∀ b∈s, y k b=0 := by
  intro s ht
  induction s using Finset.induction_on with
  | empty => exact ⟨x,.id x,rfl,fun _ _ => rfl,h,by simp⟩
  | @insert b s hb ih =>
    obtain ⟨y,hy,he,hs,h',hh⟩ := ih (fun e => ht (Finset.mem_insert_of_mem e))
    let v := -(y k b)
    let z := cast y k b v
    have hv : b≠a := by intro H; subst a; exact ht (by simp)
    refine ⟨z,Walk.transit hy (Walk.bridge y k a b v fun i _ => Or.inr (still_last a b h' hv i)), by simp [z, Ne.symm hv,he],
      fun i hi => (hs i hi).trans (near y _ _ hi _ _).symm, still_last a b h' hv v, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with hi|hi
    · subst i; simp [z,v]
    have hv' : i≠b := fun h => hb (h ▸ hi)
    simp [z,hv',hh i hi]

private lemma ta (y : Fin n → ℝ) : ∃ J : ℝ, ∀ i, y i<J :=
  ((eventually_all).mpr (fun i => eventually_gt_atTop (y i))).exists
lemma pushes {x : Points n} {k : Fin n} (h : Earliest x a k) (w : b≠a) : ∃ y : Points n,
    Walk n x y ∧ (∀ i≠k, x i=y i) ∧ Latest y a k ∧ (∃ t : ℝ, y k=t • basis a) := by
  obtain ⟨T,hT⟩ := ta (fun i : Fin n => x i b)
  let u := cast x k b (T-x k b)
  have hi : Walk n x u := .bridge _ _ a _ _ (fun i s => Or.inl (still_first a b h w i))
  have hx : Latest u b k := by
    refine ⟨(still_first a b h w _).1,fun i h => ?_⟩
    simp [u,near _ _ _ h,hT i]
  obtain ⟨J,hJ⟩ := ta (fun i : Fin n => u i a)
  let v := cast u k a (J-u k a)
  have hv : Walk n u v := .bridge _ _ b a _ (fun i s => Or.inr (still_last b a hx w.symm i))
  have hz : Latest v a k := by
    refine ⟨(still_last b a hx w.symm _).1,fun i h => ?_⟩
    simp [v,near _ _ _ h,hJ i]
  obtain ⟨y,hy,he,hh,H,Hq⟩ := park1 a hz (Finset.univ.erase a) (by simp)
  refine ⟨y,(hi.transit hv).transit hy,fun i hi => (near x _ _ hi _ _).symm.trans
    ((near u _ _ hi _ _).symm.trans (hh i hi)), H,y k a, ?_⟩
  ext i; by_cases h : i=a; subst i; simp; simp [Hq i (by simp [h]),h]

lemma after {x : Points n} {k : Fin n} (h : arranged a x) {y : Points n} (hy : ∀ i≠k, x i=y i) (ht : Latest y a k) :
    arranged a y := by
  intro s t he
  by_contra H
  by_cases E : s=k
  · subst s; exact (ht.2 t (Ne.symm H)).ne' he
  by_cases e : t=k
  · subst t; exact (ht.2 s H).ne he
  exact H (h (show _ from by dsimp only; rw [hy s E, hy t e]; exact he))

lemma line (w : a≠b) (x : Points n) (h : arranged a x) (N : Finset (Fin n))
    (H : ∀ i∉N, (∃ t : ℝ, x i=t • basis a) ∧ ∀ j∈ N, x j a < x i a) : ∃ y, Walk n x y ∧ y∈conf n ∧ onLine a y := by
  induction N using Finset.strongInductionOn generalizing x with
  | _ N ih =>
    rcases N.eq_empty_or_nonempty with hv|hh
    · subst N; exact ⟨x,.id _, also a h,fun i => (H i (by simp)).1⟩
    obtain ⟨i,hi,hz⟩ := Finset.exists_min_image N (fun i => x i a) hh
    have hu : Earliest x a i := by
      refine ⟨also a h,fun j hj => ?_⟩
      by_cases e : j∈N
      · exact lt_of_le_of_ne (hz j e) (arranged_ne a h hj.symm)
      exact (H j e).2 _ hi
    obtain ⟨y,he,hD,hv,Hl⟩ := pushes a b hu w.symm
    have hr : ∀ j∉ N.erase i, (∃ t : ℝ, y j=t • basis a) ∧ ∀ k∈N.erase i, y k a < y j a := by
      intro j h'
      by_cases p : i=j
      · subst j; exact ⟨Hl,fun j hj => hv.2 _ (Finset.mem_erase.mp hj).1⟩
      have hr := H j (fun hi => h' (Finset.mem_erase.mpr ⟨Ne.symm p,hi⟩))
      refine ⟨by rw [← hD j (Ne.symm p)]; exact hr.1,fun k hk => ?_⟩
      rw [← hD k (Finset.mem_erase.mp hk).1,← hD j (Ne.symm p)]; exact hr.2 _ (Finset.mem_erase.mp hk).2
    obtain ⟨z,hI,hv',hp⟩ := ih (N.erase i) (Finset.erase_ssubset hi) y (after a h hD hv) hr
    exact ⟨z, Walk.transit he hI,hv',hp⟩
where arranged_ne (a) {x : Points n} (h : arranged a x) {i j} (e : i≠j) : x i a≠x j a := h.ne e

private lemma fills (x : Points n) : x∈closure {x : Points n | arranged a x} := by
  let v := points fun i : Fin n => (↑(i.val):ℝ) • basis a
  let z := fun t : ℝ => x+t • v
  have he : Tendsto z (𝓝[>] 0) (𝓝 x) := by
    have h : Continuous z := continuous_const.add (continuous_id.smul continuous_const)
    simpa [z] using (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hu : ∀ᶠ t in 𝓝[>] 0, ∀ i j, i≠j → z t i a≠ z t j a := by
    apply eventually_all.mpr; intro i; apply eventually_all.mpr; intro j
    by_cases h : i=j
    · exact Eventually.of_forall fun _ hx => (hx h).elim
    have hh : (i.val:ℝ)≠j.val := by exact_mod_cast (show i.val≠j.val from fun p => h (Fin.ext p))
    by_cases hi : x i a=x j a
    · filter_upwards [self_mem_nhdsWithin] with t ht Hh
      have hr : t≠0 := LT.lt.ne' ht
      simp [z,v,hi,hr]; exact fun hy => h (Fin.ext hy)
    have hp := he.eventually (show ({x : Points n | x i a ≠ x j a} : Set _) ∈ _ from
      (isOpen_ne_fun (by fun_prop : Continuous (fun x : Points n => x i a)) (by fun_prop)).mem_nhds hi)
    exact hp.mono fun x h _ => h
  apply mem_closure_of_tendsto he (hu.mono fun i hi => show arranged a (z i) from fun j k h => by_contra fun hg => hi j k hg h)

theorem global {G : Gauge} {L : Register G} (S : Table L) (H : S.Hierarchy) (W : DiffPlan S) (T : SpinRows S) (P : W.Derivatives S)
    (C : commutes W T) (Y : Collinear W T) {n : ℕ} (x : Points n) (hx : x∈conf n) : Still W T x := by
  let a : Axis := 0; let b : Axis := 1
  have he i (h : arranged (n := n) a i) : Still W T i := by
    obtain ⟨p,ht,hP,ha⟩ := line a b (by norm_num [a,b]) i h Finset.univ (by simp)
    exact along W T H P Y C ht (fun k g => Y _ _ _ k _ hP ha)
  obtain ⟨f,hf,hv⟩ := mem_closure_iff_seq_limit.mp (fills a x)
  intro q K
  have ht := (ac W T H hx K q).continuousAt.tendsto.comp hv
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun i => (he _ (hf i) q K).symm))
end YM.Ward
