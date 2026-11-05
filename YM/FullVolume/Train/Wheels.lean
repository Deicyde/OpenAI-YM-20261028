import YM.FullVolume.Train.Astute
/-! Adapt Ground&Priced for positivity emission at Roots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid
open Work.F06 (sqLength pairingRe countCeil)
open Work.F07 (Band)
open scoped Topology BigOperators ComplexConjugate
variable {j : ℕ}

lemma strongBottom (k l : ℝ) (hk : 0<k) (hl : 0≤l) (hj : 4≤j) :
    ∃ γ σ v C : ℝ, 0<γ ∧ 0<σ ∧ 0<v ∧ 0<C ∧
      ∀ (A : RG.Clip), A.direct ≤ γ → ∀ R : Train j, ∃ M : Bed, Defined k l R M ∧
        M.covered σ C ∧ (∀ n, Floor M A n v C) ∧ (∀ n G, Bid.Sworn M n G) ∧
        (∀ n,(M.roots.acts n).PosSemidef) ∧ (R=Train.top j → ∀ n,M.diagonal.acts n=1) := by
  let w (i : Train j) := i
  obtain ⟨η,G,hη,hG,h⟩ := heart_banked k hk hj w
  have hh := (heart_heats k hk hj w).1
  have hg := (insurance k l hk hl hj w).1
  obtain ⟨a,X,ha,hX,hf⟩ := hh.funds
  obtain ⟨b,Y,hb,hY,hJ⟩ := hg.funds
  obtain ⟨ρ,U,hρ,hU,hb'⟩ := hg.stock.uniform
  have hR := pledge_warm k l hk hl hj w
  obtain ⟨μ,V,hμ,hV,hV'⟩ := hR.stock.uniform
  let γ := b/2; have hγ : 0<γ := by unfold γ; linarith
  let C := U+γ+Y
  let paid (c : Clip) (R : Train j) := minusRows (amend k l R) (scaleRows c.direct (unitRow (TypeFace 2)))
  obtain ⟨s,Q,ν,hs,hν,h'⟩ := Work.F07.answer (TypeFace 2) C γ ρ hγ hρ
  have he : 0 ≤ max Q 0 := le_max_right ..
  let σ := min η (min ρ (min μ ν))
  let B := X+Y+V+U+G+max Q 0
  have hB : 0<B := by unfold B; linarith
  refine ⟨γ,σ,min a b,B,hγ,lt_min hη (lt_min hρ (lt_min hμ hν)),lt_min ha hb,hB,fun p hp R => ?_⟩
  have hr : (amend k l R).strip ρ U := by simpa only [w,mul_one] using hb' R
  have ht : (paid p R).strip ρ C := by
    unfold paid
    apply strip_mono (strip_minus hr (strip_scale strip_unit _)) le_rfl
    rw [Real.norm_eq_abs,abs_of_pos p.quadratic_pos,mul_one]; unfold C; linarith
  obtain ⟨F,hχ,hF,hA⟩ := h' (paid p R) ht
    (low_ceiling (hJ R) p hp _ (by unfold C; linarith) ⟨ρ,U,hρ,hr⟩)
  let M : Bed := ⟨pink k R,blue k R,amend k l R,pledge k l R,F⟩
  refine ⟨M,⟨rfl,rfl,rfl,rfl⟩,?_,?_,?_,fun n=>Retort.warmly hs hν hF hχ n,?_⟩
  · have hQ : Q≤max Q 0 := le_max_left ..
    refine ⟨strip_mono (h R).1 (min_le_left ..) ?_, strip_mono hr ((min_le_right ..).trans (min_le_left ..)) ?_, strip_mono (hV' R) ((min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..))) ?_, strip_mono hF ((min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..))) ?_,strip_mono (h R).2 (min_le_left ..) ?_⟩ <;> unfold B <;> linarith
  · intro n
    obtain ⟨_,h₁,h₂,h₃,h₄,h₅⟩ := obligations k l hk hl hj R n
    obtain ⟨he,hq⟩ := heart_inverse k hk hj R n
    obtain ⟨hs,hm⟩ := obey_band _ (hg.stock.whole R) (hJ R) n
    obtain ⟨hv,hy⟩ := obey_band _ (hh.stock.whole R) (hf R) n
    have hbZ (T : Row (TypeFace 2) (TypeFace 2)) (K V) (hN : Numeric (T.acts n) K V) (hA : min a b≤K) (hB : V≤B) : Numeric (T.acts n) (min a b) B := by
      intro v
      have hv : 0≤ dotProduct v v := by unfold dotProduct; apply Finset.sum_nonneg; intro k _; rw [← sq]; positivity
      exact ⟨(mul_le_mul_of_nonneg_right hA hv).trans (hN v).1,(hN v).2.trans (mul_le_mul_of_nonneg_right hB hv)⟩
    refine ⟨he,h₁.1,?_,forced_amend k l hk hl hj R,h₂,⟨h₄,hq.1⟩,hbZ _ b Y hm (min_le_right ..) (by unfold B; linarith), hbZ _ a X hy (min_le_left ..) (by unfold B; linarith)⟩
    rw [full_cover,show M.roots=F from rfl,← (hA n).1];
    unfold paid; rw [Whole.less (hg.stock.whole R) ((Whole.coin _).weight _) _,acts_scale,acts_unit]; simp; rfl
  · intro n G; exact sworn_metric k l hk hl hj R n M rfl G
  intro hT n
  change (record (pulse k R)).acts n=1
  subst R
  have he := Whole.eq_on (hh.stock.whole (Train.top j)) (Whole.coin (TypeFace 2)) (fun p hp => Eq.trans ((heart_true k hk hj (Train.top j)).1.echo _ hp) ((top_metric k hk j (base_subset_realCube zone_pos hp)).2.trans (read_unit _ p).symm)) n
  exact he.trans (acts_unit n)

def PeakQuote (K : KernelChoices) (j : ℕ) (m γ σ η C : ℝ) := ∀ (p : Clip), p.direct≤γ → ∀ R : Train j,
    ∃ M : Bed, Defined K.penalty m R M ∧ M.covered σ C ∧ (∀ n, Floor M p n η C) ∧ (∀ n G, Bid.Sworn M n G) ∧
      (∀ n,(M.roots.acts n).PosSemidef) ∧ (R=Train.top j → ∀ n,M.diagonal.acts n=1)
structure Marvel (K : KernelChoices) (q : MapPrices) (l γ : ℕ → ℝ) (b : ℕ → ℕ) : Prop where
  net i : 0 ≤ l i
  fit i : 0 < γ i
  bottom (j:ℕ) : 4 ≤ j → PeakQuote K j (l j) (γ j) (q.α j) (q.η j) (q.Ω j)
  hop (j t:ℕ) : Mag j t → HopQuote K j t (l j) (l t) (q.α j) (q.η j) (q.Ω j) (b j)

lemma PeakQuote.revise {K : KernelChoices} {j : ℕ} {γ m σ η C σ' η' C' : ℝ} (h : PeakQuote K j m γ σ η C) (ht : σ'≤σ) (hk : η'≤η) (hC : C≤C') : PeakQuote K j m γ σ' η' C' := by
  intro p hp R; obtain ⟨M,h₁,h₂,h₃,h₄,hZ,h₅⟩ := h p hp R
  exact ⟨M,h₁,cover_revise h₂ ht hC, fun n => floor_revise (h₃ _) hk hC,h₄,hZ,h₅⟩
lemma reapsY (K : KernelChoices) : ∃ q l γ b,Marvel K q l γ b := by
  classical
  choose δ hδ h using buys K
  let l := fun i : ℕ => max (δ i i) (δ (i+1) i)
  have hl (i) : 0 ≤ l i := (hδ i i).le.trans (le_max_left ..)
  have hH (j t : ℕ) : ∃ σ η C : ℝ, ∃ b : ℕ, 0 < σ ∧ 0 < η ∧ (Mag j t → HopQuote K j t (l j) (l t) σ η C b) := by
    by_cases hp : Mag j t
    · apply h j t _ _ (hl _)
      rcases hp.2.2 with ht|ht
      · rw [ht]; exact le_max_left ..
      rw [← ht]; exact le_max_right ..
    exact ⟨1,1,1,1,one_pos,one_pos,fun hh => False.elim (hp hh)⟩
  choose S E T n hS hE hT using hH
  have hb (j : ℕ) : ∃ γ σ η C : ℝ, 0<γ ∧ 0<σ ∧ 0<η ∧ (4≤j → PeakQuote K j (l j) γ σ η C) := by
    by_cases he : 4 ≤ j
    · obtain ⟨γ,σ,η,C,hγ,hσ,hη,hC,h⟩ := strongBottom K.penalty (l j) K.penalty_pos (hl j) he
      exact ⟨γ,σ,η,C,hγ,hσ,hη,fun _ => h⟩
    exact ⟨1,1,1,1,one_pos,one_pos,one_pos,fun hz => False.elim (he hz)⟩
  choose γ t e u hγ ht he hu using hb
  let X : MapPrices := ⟨fun i => min (t i) (min (S i i) (S i (i-1))),
    fun i => max (u i) (max (T i i) (T i (i-1))),fun i => min (e i) (min (E i i) (E i (i-1))),
    fun i => lt_min (ht i) (lt_min (hS ..) (hS ..)),fun i => lt_min (he i) (lt_min (hE ..) (hE ..))⟩
  refine ⟨X,l,γ,fun i => max (n i i) (n i (i-1)),⟨hl,hγ,fun i hi => ?_,fun i j hij => ?_⟩⟩
  · exact (hu i hi).revise (min_le_left ..) (min_le_left ..) (le_max_left ..)
  apply (hT i j hij).revise
  all_goals
    rcases (show j=i ∨ j=i-1 by obtain hx := hij.2.2; omega) with hz|hz <;> rw [hz] <;> (try dsimp [X]) <;> grind

variable {G:Gauge}

def glow (A:Levels G)(l:ℕ→ℝ)(N i:ℕ):= (destination A N i).rollFunds A.clock.kernel.penalty (l (A.clock.J (i+1))) (l (A.clock.J i))
structure Exhibits (A:Levels G)(X:MapPrices) (M:Horizon A) (l: ℕ→ℝ):Prop where
  classic : Craft.Rack A X M
  offered : Present A M l
  vivid N m (h:m≤N) (p:Side) : ((M.H N m).roots.acts p).PosSemidef
  deposits N i : i < N →
    let j:= A.clock.J (i+1); let P:= glow A l N i
    P.strip (X.α j) (X.Ω j) ∧ Funds P (X.η j) (X.Ω j) ∧ ∀ p,
      Bleeps (A.clock.op i p).ratio (M.H N (i+1)) (M.H N i) (M.towers N i) A.clock.kernel.penalty P
lemma wardrobe (A : Levels G) (X : MapPrices) (l γ b) (h : Marvel A.clock.kernel X l γ b) (ht : Credit A γ b) :
    ∃ M : Horizon A, Exhibits A X M l := by
  classical
  let K := A.clock.kernel
  choose H hH h1 h2 h3 hχ h4 using fun i N => h.bottom _ (A.clock.adm i) _ (ht.1 i) (location A N i)
  let M : Horizon A := ⟨fun N i => H i N,fun N i => (destination A N i).duo K.penalty⟩
  have hm (i N : ℕ) : Mag (A.clock.J (i+1)) (A.clock.J i) := by
    let P := destination A N i; have ht := P.narrow; have hh := P.mono
    exact ⟨A.clock.adm _,A.clock.adm _,by omega⟩
  have hr N i (hi:i<N) : let j:= A.clock.J (i+1); let P:= glow A l N i
                            P.strip (X.α j) (X.Ω j) ∧ Funds P (X.η j) (X.Ω j) ∧ ∀ p,Bleeps (A.clock.op i p).ratio (M.H N (i+1)) (M.H N i) (M.towers N i) K.penalty P :=by
    let P := destination A N i
    obtain ⟨hb,he,hf⟩ := h.hop _ _ (hm i N) P
    let Q := P.rollFunds K.penalty (l (A.clock.J (i+1))) (l (A.clock.J i))
    refine ⟨he,hf (ht.2 i),?_⟩
    intro p; have hh : location A N i=P.land := loc_land A N i hi
    exact check_bleep K (l (A.clock.J i)) (l (A.clock.J (i+1))) (h.net _) (h.net _) P (A.clock.adm i)
        (H (i+1) N) (H i N) (hH (i+1) N) (hh ▸ hH i N) (c:=A.S.side i p) (f:=A.S.side (i+1) p) (A.S.oneStep i p).exact_size
  refine ⟨M,?_,⟨fun N i _ => hH i N,fun _ _ _ => ⟨rfl,rfl⟩⟩,fun _ _ _ _ =>hχ ..,hr⟩
  constructor
  · intro N i hi; exact h1 _ _
  · intro N i hi n; exact h2 _ _ n
  · intro N i n hi; exact h3 _ _ _ _
  · intro N n; exact h4 _ _ (loc_top A N) n
  · intro N i hi
    exact (h.hop _ _ (hm i N) (destination A N i)).1
  · intro N i p hi; let P := destination A N i
    have hh : (location A N i)=P.land := loc_land A N i hi
    have he := (A.S.oneStep i p).exact_size
    exact diagonal K (l (A.clock.J i)) (l (A.clock.J (i+1))) (h.net _) (h.net _) P (A.clock.adm i)
      (H (i+1) N) (H i N) (hH (i+1) N) (hh ▸ hH i N) (c:=A.S.side i p) (f:=A.S.side (i+1) p) he
  intro N i hi; obtain ⟨he,hs,hj⟩:=hr N i hi; exact ⟨glow A l N i,he,fun p hp=> ⟨(hs p hp).1,fun x=> ((hs p hp).2 _).1⟩,hj⟩
end YM.Next.Free
