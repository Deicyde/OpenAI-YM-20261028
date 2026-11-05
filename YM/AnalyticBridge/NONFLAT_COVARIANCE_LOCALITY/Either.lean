import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Cover
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Plant

/-!
# Direction and entry agreements

Local through the full branches, T and timestep cannot change. Both readings
of a panel coordinate paid with a bounded multiple of B. Use larger supports
for eligibility past the Gaussian; this doesn't assert the encoding or sizes
of any coarse representation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality.Matching
open Function Filter Lattice RG Pressure Pressure.Stores Precision Wilson Tree Matrix
open Next.SectorChange Next.SectorChange.Schur Next.SectorChange.Wisps Next.Fluctuations
open Next.SectorChange.Completion Next.SectorChange.Rows Full Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

variable {V W : Config G c} {A B : Stores S} {F H : Forest S.ratio} {k k' : S.Choices}
    {P : Teller G} {T : Tube G S} {o : Site c} {r : ℕ}

/-- Numeric sublist of D argument reads, tree/calculation fixed for this lemma. -/
lemma ReadsWithin.bump_eq (hp : P.Funds S T) (hx : ReadsWithin o r A B F H V W k k')
    (a : Directions G f) (p : Receipt G S) (h : separation o (down S p)+span S.patch x ≤ r) :
    Rows.bump T x V k a p.1=Rows.bump T x W k' a p.1 := by
  obtain ⟨⟨s,i|i⟩,t⟩ := p
  · change separation o (s.act (S.ratio.parent i.1.1))+_ ≤ r at h
    change Rows.faceKick T x V a s i=Rows.faceKick T x W a s i
    rcases i with ⟨j, b|b⟩
    · simp only [Rows.faceKick,Bool.false_eq_true,↓reduceIte]
      rw [jet_reads_face a j (W:=W) _]
      apply hx.sites.shrink
      change separation o (s.act (S.ratio.parent j.1))+_≤r at h
      unfold span at *; omega
    · obtain ⟨m,n,H,-⟩ := hp.feeds
      rw [face_series _ _ _ _ _ _ H,face_series _ _ _ _ _ _ H]
      apply Finset.sum_congr rfl
      intro p hq; rw [pulse_reads_face a j.1 p (W:=W) _]
      apply hx.sites.shrink
      have he := (on_spool ..).1 hq
      change separation o (s.act (S.ratio.parent j.1))+_≤r at h
      unfold span at *; omega
  change separation o (s.act i.1)+_≤r at h
  unfold span at h
  let q := sendEdge s 0 i
  have hz : separation o q.1 ≤ separation o (s.act i.1) + 1 :=
    (separation_triangle o (s.act i.1) _).trans (Nat.add_le_add_left (spin_step i s) _)
  have he : separation o (q.1+step q.2) ≤ r := by
    have hf := Work.E03.sep_step q.1 q.2
    have hh := separation_triangle o q.1 (q.1+step q.2); omega
  have hv : separation o q.1 ≤ r := by omega
  simp only [Rows.bump,Rows.noiseKick,Sum.elim_inr,
    jet_reads_prediction (funds_branch hp) i s k k' (hx.choices _ hv)
      (hx.choices _ he) (hx.bonds _ hv) a (hx.sites.shrink (by omega))]

lemma ReadsWithin.feature_eq (hp : P.Funds S T) (hx : ReadsWithin o r A B F H V W k k')
    (p : Receipt G S) (h : separation o (down S p) + span S.patch x+10*radiusB x+4 ≤ r) :
    ∀ i, feature x T A F k V p i=feature x T B H k' W p i := by
  intro i
  by_cases hz : separation (down S p) (point S i) ≤ span S.patch x
  · have hh := separation_triangle o (down S p) (point S i)
    have hf := hx.correspond x p h
    have hl : engaged x A F i.1 ↔ engaged x B H i.1 := hx.enabled x
      (by change separation o (point S i)+_+_≤_; omega)
    have ha := hx.bump_eq (x:=x) hp (longPulse i) p (by omega)
    rw [feature,feature,Matrix.of_apply,Matrix.of_apply]
    by_cases h : engaged x A F i.1
    · rw [if_pos h,if_pos (hl.mp h)]
      change (Rows.restrict x _ A F _ p.1) p.2=(Rows.restrict x _ B H _ p.1) p.2
      by_cases hZ : keep x (shots S x) A F p.1
      · unfold Rows.restrict; rw [if_pos hZ, if_pos (hf.mp hZ),ha]
      unfold Rows.restrict; rw [if_neg hZ,if_neg (mt hf.mpr hZ)]
    rw [if_neg h,if_neg (mt hl.mpr h)]
  rw [feature_range (funds_branch hp) A p i hz, feature_range (funds_branch hp) B p i hz]

abbrev here (x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c) (k : S.Choices) := board x A F G (Rows.gram T x V k (shots S x) A F)
lemma once (x : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c) (k : S.Choices) (z : Coord G c) : deck x A F V k T z=here x T A F (coarse V z) k := rfl

-- range/support price in *integer native parent sites*; use later with halo bounds
def extent (P : Patch) (x : ℝ) := 2*span P x
def room (P : Patch) (x : ℝ) := extent P x + 10*radiusB x + 4

lemma deck_quiet (hp : S.patch.Branches S.kernel G) (x : ℝ) (T : Tube G S) (A : Stores S)
    (F : Forest S.ratio) (V : Config G c) (k : S.Choices) (p q : Index G f)
    (hi : ¬ separation (point S p) (point S q) ≤ extent S.patch x) :
    here x T A F V k p q=0 := by
  unfold extent at hi
  unfold here; rw [from_data x T A F V k]
  rw [Matrix.add_apply]; change (∑ r : Receipt G S, _)+_=0
  rw [identityRest,Matrix.diagonal_apply_ne]
  · rw [add_zero]; refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : separation (down S i) (point S p) ≤ span S.patch x
    · have ht : ¬separation (down S i) (point S q) ≤ span S.patch x := by
        intro he; have hh := separation_triangle (point S p) (down S i) (point S q)
        rw [separation_comm (point S p) (down S i)] at hh; omega
      simp only [feature_range hp A i q ht,mul_zero]
    simp only [Matrix.transpose_apply,feature_range hp A i p h,zero_mul]
  exact fun e => hi (by simp [e])

lemma ReadsWithin.here_first (hp : P.Funds S T) (hx : ReadsWithin o r A B F H V W k k')
    (p : Index G f) (h : separation o (point S p)+room S.patch x ≤ r) (i : Index G f) :
    here x T A F V k p i=here x T B H W k' p i := by
  unfold room extent at h
  unfold here; rw [from_data x T A F V k,from_data x T B H W k']
  have ht : identityRest x A F G p i=identityRest x B H G p i := by
    have he := hx.enabled x (e:=p.1) (by change separation o (point S p)+_+_ ≤ r; omega)
    unfold identityRest; simp_rw [Matrix.diagonal_apply]; split
    · simp only [he]
    rfl
  simp only [Matrix.add_apply,ht,add_left_inj, Matrix.mul_apply, transpose_apply]
  refine Finset.sum_congr rfl fun i' _ => ?_
  by_cases he : separation (down S i') (point S p) ≤ span S.patch x
  · have hv := hx.feature_eq hp i' (show separation o (down S i')+span S.patch x+10*radiusB x+4 ≤ r from
        (by have hh := separation_triangle o (point S p) (down S i'); rw [separation_comm] at he; omega))
    rw [hv,hv]
  simp [feature_range (funds_branch hp) A i' p he, feature_range (funds_branch hp) B i' p he]

lemma here_sym (p q : Index G f) : here x T A F V k p q=here x T A F V k q p := by
  have he := (deck_symm (x:=x) A F T V (0:Coord G c) k).apply q p
  rw [once,coarse_zero] at he
  exact he

lemma ReadsWithin.here_last (hp : P.Funds S T) (hx : ReadsWithin o r A B F H V W k k')
    (p : Index G f) (h : separation o (point S p)+room S.patch x ≤ r) (i : Index G f) :
    here x T A F V k i p=here x T B H W k' i p :=
  (here_sym i p).trans ((hx.here_first hp p h i).trans (here_sym ..))
end YM.AnalyticBridge.NonflatCovarianceLocality.Matching
