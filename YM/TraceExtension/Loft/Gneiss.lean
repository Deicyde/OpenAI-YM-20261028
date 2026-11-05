import YM.TraceExtension.Loft.Skis
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric
open scoped BigOperators Topology ContDiff ComplexConjugate
variable {ι κ α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n:ℕ}{σ τ A C D μ δ ε a r:ℝ}
def sizeV (α β:Type)[Fintype α][Fintype β](A:ℝ):= Fintype.card α * (Fintype.card β * A)
lemma size_v {M:CompM α β}(h:∀ i j, ‖M i j‖ ≤ A)(he:0  ≤  A): vflux M  ≤  sizeV α β A:=by
    have hx:sizeV α β A= (Fintype.card α:ℝ)*(Fintype.card β * A):=rfl
    apply flux_price (by rw[hx]; positivity); intro u v; unfold dotProduct mulVec; simp_rw[dotProduct,Finset.mul_sum]; refine (norm_sum_le ..).trans ((sum_le_sum fun i _=>norm_sum_le ..).trans ?_)
    calc
     _  ≤  ∑ i:α,∑ j:β, slug u * (A * slug v) := by
        refine sum_le_sum fun i _=> sum_le_sum fun j _=>?_ ; simp only [norm_mul]; exact mul_le_mul (slug_atom u i) (mul_le_mul (h i j) (slug_atom v j) (norm_nonneg _) he) (by positivity) (slug_nonneg _)
     _ = _ := by rw[hx]; simp; ring
lemma basic_c (p q:Momentum)(K:CompM α β): carryM (Slab.basic α) (Slab.basic β) p q K = K:=by simp [carryM,Slab.basic]
lemma basic_w {p q:Momentum}{K:CompM α β} : serial (Slab.basic α) (Slab.basic β) p q K C ↔ vflux K  ≤  C:=by simp [serial,basic_c]
abbrev Skew (F:Film ι α β)(σ C:ℝ):= Charges (Slab.basic α) (Slab.basic β) F σ C
lemma reverse_h {F:Film ι α β}(h:Skew F σ C): Skew F.rear σ C:=by
    have hv:= h.rear
    have hk(X:Type)[Fintype X][DecidableEq X]: (Slab.basic X).dual=Slab.basic X := by unfold Slab.dual Slab.basic; simp
    rwa[hk,hk] at hv
lemma post_cap {K: Momentum → CompM α β}(h:Poster σ K)(he:τ<σ)(ht:0  ≤  τ): ∃ A:ℝ,0 ≤  A ∧ ∀ p∈strip τ, vflux (K p) ≤ A:=by
    have hv(p:Momentum)(hp:p ∈ pier τ):p∈strip σ:=fun i=> (hp.2 i).trans_lt he
    have hh(i j): ∃ C:ℝ, 0 ≤ C ∧ ∀ p∈pier τ, ‖K p i j‖ ≤ C:=by
        obtain ⟨A,hA⟩:= ((pier_compact τ ht).image_of_continuousOn (f:=fun p=>‖K p i j‖) (fun p hp=> ((h.shape (hv p hp) i j).continuousAt.norm).continuousWithinAt)).bddAbove; exact ⟨max A 0,le_max_right .., fun p hp=> le_trans (hA ⟨p,hp,rfl⟩) (le_max_left ..)⟩
    choose C hC H using hh; let S:= ∑ i, ∑ j,C i j; have hS:0  ≤  S:=sum_nonneg fun i _=> sum_nonneg fun j _=> hC i j
    refine ⟨sizeV α β S,by unfold sizeV; positivity,fun p hp=>?_⟩
    obtain ⟨x,hx,hR⟩:=Nave.roll p; have hP:=skyPeriod hp hR.symm
    have hQ:x∈pier τ:=⟨hx,fun j=> (hP j).le⟩; rw[← h.shifts hR (hv _ hQ)]; exact size_v (fun i j=> ((H i j _ hQ).trans (single_le_sum (s:=univ) (f:=C i) (fun k _=>hC i k) (mem_univ j))).trans (single_le_sum (s:=univ) (f:=fun i=>∑ j,C i j) (fun i _=>sum_nonneg fun j _=>hC i j) (mem_univ i))) hS
set_option maxHeartbeats 800000 in
lemma matt_w (G:Gauge)(h:0 < σ): ∃ A:ℝ, 0  ≤  A ∧ Skew (matina G) σ A:=by
    let X:= firstB G
    let A:= vflux (X.tab 0); let B(i:Fslot G):=vflux (X.spot i 0 0); let C (i j:Fslot G):=vflux (X.arch i j 0 0 0); let S:=∑ i,B i; let P:=∑ i,∑ j,C i j; let a:=A+S+P
    have hB(i):0  ≤  B i:= flux_nonneg _;have hA:0 ≤ A:=flux_nonneg _;have hC (i j):0 ≤  C i j:=flux_nonneg _;have hs:0  ≤  S:=sum_nonneg fun i _=>hB i;have hp:0  ≤  P:=sum_nonneg fun i _=>sum_nonneg fun j _=> hC i j
    have hv : Skew X σ a:=by
        have hx : Play X σ:=⟨Poster.web _,fun _ => ⟨fun _ => BillD.park _ _,fun _ _ _ =>rfl⟩,fun _ _=> ⟨fun _ => BillD.park _ _,fun _ _ _ _=>rfl⟩⟩
        refine ⟨hx,fun _=> basic_w.mpr (show A ≤ a by unfold a; linarith),fun i p q _=> basic_w.mpr (show B i ≤ a from (single_le_sum (f:=B) (fun j _=> hB j) (mem_univ i)).trans (show S ≤ a by unfold a; linarith)), fun i j p q r _=>?_⟩
        refine basic_w.mpr (show C i j ≤ a from ?_); calc
         C i j  ≤  ∑ j,C i j:=single_le_sum (s:=univ) (fun k _=> hC i k) (mem_univ j)
         _  ≤  P := single_le_sum (s:=univ) (f:=fun l=>∑ j,C l j) (fun l _=>sum_nonneg fun k _=> hC l k) (mem_univ i)
         _  ≤  a:=by unfold a; linarith
    obtain ⟨L,hL,H⟩:=post_cap (K:=pageD G 0) (page_linen 0) (lt_add_one σ) h.le
    have hT: Skew (firstRay G) σ L:=by
        have hy:=Poster.plus_nec (σ:=σ) (f:=pageD G 0) (page_linen 0) (-1); simp only[neg_smul,one_smul] at hy
        exact Charges.current hy hL (fun p hp=> basic_w.mpr (le_trans (flux_neg _|>.le) (H p hp)))
    let D:=vflux (dashboard G); have hD:0 ≤ D:=flux_nonneg _
    have hz: Skew (boardF G) σ (D+L):=Charges.current ((Poster.web _).amounts (page_linen 0)) (by positivity) (fun p hp=>basic_w.mpr ((flux_plus ..).trans (add_le_add_right (H p hp) D)))
    have hw:=hT.plus (hv.pay hz h);exact ⟨_,hw.funds h,hw⟩
lemma wine_f (b: Picture G (n+1))(h:∀ i j,Firm σ A (b i j)) (he:0 ≤ A)(v:Fin n → Momentum)(i:Fin n →  Fslot G)(p:Momentum)(hx:∀ i,v i∈strip σ)(hw:p∈strip σ)(hv:p+∑ i,v i∈strip σ):vflux (wineM b v i p) ≤ sizeV (Fslot G) (Fslot G) A:=by
    have hL(j):wineShift v p j∈strip σ:=by
      cases j using Fin.lastCases with
      | last => simpa only [wineShift,duoTop,Fin.snoc_last]
      | cast j => cases j using Fin.lastCases with
         | last=>simpa only[wineShift,duoTop,Fin.snoc_castSucc,Fin.snoc_last] using negResident hv
         | cast j=>simpa only[wineShift,duoTop,Fin.snoc_castSucc] using hx j
    refine size_v (fun j k=>?_) he; let r:=duoTop n i j k; exact (h (Prod.snd∘r) (Prod.fst∘r)).2 (caftan (t:=n+1) (wineShift v p)) fun i=> hL _ i.2
lemma jar_sk {V:Jar G}(h:V.fees σ C)(he:0 ≤ C): Skew V.cast σ (sizeV (Fslot G) (Fslot G) C):=by
   refine ⟨h.live,fun {p} hp=>basic_w.mpr (wine_f (n:=0) _ h.1 he ![] ![] p (fun i=>Fin.elim0 i) hp (by simpa)),fun i p q w=>?_,fun i j p q r w=>?_⟩
   · exact basic_w.mpr (wine_f (n:=1) _ h.2.1 he ![p] ![i] q (fun j=>by fin_cases j; exact w.side) w.basic (by simpa using w.added))
   exact basic_w.mpr (wine_f (n:=2) _ h.2.2 he ![p,q] ![i,j] r (fun a=>by fin_cases a; exact w.oneWay.side; exact w.second.side) w.oneWay.basic (by rw[Fin.sum_univ_two];exact w.total))
lemma ices (α κ:Type)[Fintype α][DecidableEq α](h: μ∈Set.Icc (0:ℝ) 1): Skew (icing α κ μ) σ 1:=by
    refine Charges.current (Poster.web _) zero_le_one (fun p _=> basic_w.mpr ?_); rw[flux_cost,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]; exact mul_le_one₀ (by nlinarith[h.1,h.2]) (flux_nonneg _) flux_one
end YM.Trace.Loft
