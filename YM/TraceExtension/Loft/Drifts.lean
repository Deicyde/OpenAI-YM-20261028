import YM.TraceExtension.Loft.Gneiss
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric
open scoped BigOperators Topology ContDiff ComplexConjugate
variable {ι κ α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {G:Gauge}{V:Jar G}{S:Skuta ι G}{μ:ι→ℝ}{σ τ A C D δ ε a r:ℝ}
lemma hotbase (F:ι → Jar G)(h:∀ i,(F i).fees σ A)(hs:0 < σ)(hA:0 ≤ A):∃ B E, 0≤B ∧ 0≤E ∧ (∀ i,Skew (granary G (F i).cast) σ B) ∧ Skew (quarry G) σ E:=by
    obtain ⟨X,hX,hx⟩:=matt_w G hs; exact ⟨sizeV _ _ A+4*X*X,4*X*X, by unfold sizeV; positivity,by positivity,fun i=>(jar_sk (h i) hA).plus (hx.pay (reverse_h hx) hs), (reverse_h hx).pay hx hs⟩
abbrev Kryst (K:Film ι α α):=Freezer (Slab.basic α) (Slab.basic α) K.tab
lemma ember_st (d:ℝ)(hd:0<d)(he:d≤δ){k: Momentum}(hp:star k=k): Stable ((cinder G δ).tab k) (d^2):=by
    have hμ:= hd.trans_le he
    intro v; rw [crumbly (G:=G) (μ:=δ) (σ:=1) zero_lt_one k (Work.F07.realStrip _ zero_lt_one hp),Matrix.smul_mulVec, one_mulVec,slug_scale]
    apply mul_le_mul_of_nonneg_right _ (slug_nonneg v); rw [show soda δ k=↑(pebWeight k δ) by unfold soda pebWeight; rw[stone_real hp];push_cast;rfl,Complex.norm_real,Real.norm_of_nonneg (peb_pos _ hμ|>.le)]; exact (pow_le_pow_left₀ hd.le he 2).trans (le_add_of_nonneg_left (sq_nonneg _))
lemma blizzard (h:S.Live σ D ε C V)(hv: V.fees σ A)(hA:0 ≤ A)(hC:0 ≤ C)(hs:0 < σ)(ht:0 < ε)(hd:0 < δ)(hp:∀ i,μ i∈Set.Icc δ 1): ∃ s B E, 0<s ∧ 0≤ B ∧ 0≤ E ∧ ∀ i, let f:= alp G (μ i) (S.useJar V i); let g:= cinder G (μ i); Skew f s B ∧ Skew g s B ∧ Kryst f s E ∧ Kryst g s E:=by
    have hm i: μ i∈Set.Icc (0:ℝ) 1:= ⟨hd.le.trans (hp i).1,(hp i).2⟩
    obtain ⟨B,E,hB,hE,hb,hq⟩:=hotbase (fun i=>(S.light i).combine V) (fun i=> (h i).2.1.pay hv) hs (by positivity)
    let L:=max (B+1) (E+1); have hL: 0 ≤ L:=le_trans (by linarith: 0 ≤ B+1) (le_max_left ..); let k:=min ε 1
    have hk: 0 < k:=lt_min ht zero_lt_one
    obtain ⟨s,z,hS,hQ,hZ,H⟩:=shelter σ L 1 (k*δ^2) hs hL zero_le_one (by positivity)
    have hw (α:Type) [Fintype α][DecidableEq α] (K:Film (Fslot G) α α)(hK:Skew K σ L)(he: ∀ p, star p=p → Stable (K.tab p) (k*δ^2)): Kryst K s z:=by
       refine H _ (Slab.basic α) (Slab.basic α) Slab.Height.basic Slab.Height.basic K.tab hK.covered.tab (fun p hp=>hK.base hp) (fun p hp=>?_); rw[basic_c]; exact he p hp
    refine ⟨s,L,z,hS,hL,hZ, fun i=>?_⟩; dsimp only
    let F:= alp G (μ i) (S.useJar V i)
    have hf:Skew F σ L:= ((hb i).plus (ices (Fslot G) (Fslot G) (hm i))).mono le_rfl (le_max_left ..); let Q:= cinder G (μ i); have hh: Skew Q σ L:=(hq.plus (ices _ _ (hm i))).mono le_rfl (le_max_right ..)
    refine ⟨hf.mono hQ le_rfl,hh.mono hQ le_rfl,hw _ _ hf (fun p H=>?_ ), hw _ _ hh (fun p H=>?_)⟩
    · refine Stable.mono (alp_w (μ:=μ i) (h i).1 H) (mul_le_mul_of_nonneg_left ?_ hk.le); exact (pow_le_pow_left₀ hd.le (hp i).1 2).trans (le_add_of_nonneg_left (sq_nonneg _))
    exact (ember_st δ hd (hp i).1 H).mono (mul_le_of_le_one_left (sq_nonneg _) (min_le_right ..))
lemma quick_f {T:KindF G}(h:Skew (alp G δ T) σ A)(he:Skew (cinder G δ) σ A) (hp:Kryst (alp G δ T) σ C) (hv:Kryst (cinder G δ) σ C)(hs:0 < σ) (i j):
    let X:=fun n:ℕ => ↑n*(C*A+C*A*C*A)
    Firm (σ/2) (‖((↑(1/2:ℝ)):ℂ)‖*X (Fintype.card (Fslot G))+X (Fintype.card (Foot G))) (starTrack (quick δ G T i j)):= (((Firm.const (half_pos hs) ((↑(1/2:ℝ)):ℂ)).mul (hp.figure h hs i j)).sub (hv.figure he hs i j))
lemma banana (h:S.Live σ D ε C V)(hv: V.fees σ A)(hA:0 ≤ A)(hC:0 ≤ C)(hs:0 < σ)(ht:0 < ε)(hd:0 < δ)(hp:∀ i,μ i∈Set.Icc δ 1) : ∃ s B, 0<s ∧ 0 ≤ B ∧ ∀ w i j, Firm s B (starTrack (quick (μ w) G (S.useJar V w) i j)):=by
    obtain ⟨s,b,e,H,hB,hE,hk⟩:=blizzard h hv hA hC hs ht hd hp
    let X:=fun n:ℕ => ↑n*(e*b+e*b*e*b)
    exact ⟨s/2,‖((↑(1/2:ℝ)):ℂ)‖*X (Fintype.card (Fslot G))+X (Fintype.card (Foot G)), half_pos H, by unfold X; positivity, fun w i j=> quick_f (hk w|>.1) (hk w|>.2.1) (hk w|>.2.2.1) (hk w|>.2.2.2) H i j⟩
end YM.Trace.Loft
