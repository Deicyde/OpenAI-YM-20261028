import YM.RG08.Pivot.Snap
/-!
# Step passes Wick normal-ordering at the letter. `W ψ` is full bulk G,
not conditional Γ. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis Finset
open scoped Topology BigOperators
variable {A B : Type} {G : Gauge} {P : Patch} {K : KernelChoices} {t n D d r ℓ : ℕ} {v : Train ℓ}
variable {X: Repeated P.L} {w:Train P.J} {F : Air G} (σ: ChartRatio G)(i:G.ColorIndex)
variable {c f : Side}{H:Matrix (Body 1 f) (Body 1 c) ℝ} (s : f.val=c.val*P.L.val)
variable (hp : P.Branches K G) 
variable {R : ℝ} {U : BoardU D R G} {u':Matrix (Body 1 f) (Body 1 c) ℝ}{C:FreeResolvent.FaceRow}
local notation "P'" => linked P K c f s
include hp
lemma salute (X : Repeated P.L)(w:Train P.J) :
    let T:= P'; let F:=X.forest T.ratio; let Q: Matrix (Lines G f 1) (Co c (Park G P.L)) ℝ:= loomArc T.ratio; let Γ:=FreeResolvent.covariance G T F (pink K.penalty w);
    Q*(veiled (conditionalCov G X K w)).acts c*Qᵀ=Γ := by
  intro T F L C
  let R:= FreeResolvent.treeMatrix G T F (pink K.penalty w)
  let I:Matrix (Co c (Park G P.L)) (FreeResolvent.Active G F) ℝ:= chargeS T F G; let U:= sprig T F G
  have he: L*I=U:= by
    apply matrix_eq; intro v; rw [← Matrix.mulVec_mulVec]
    exact (loom_tip T.ratio (G:=G) (I *ᵥ v)).trans ((congr_arg (fineL G T.ratio) (mat_basis T F v)).trans (lodge_f ..))
  rw [show (veiled (conditionalCov G X K w)).acts c = I* R⁻¹* Iᵀ from people P K X w hp s, ← Matrix.mul_assoc,← Matrix.mul_assoc, Matrix.mul_assoc (L*I* R⁻¹), ← Matrix.transpose_mul,he]; unfold C FreeResolvent.covariance FreeResolvent.treeInverse FreeResolvent.resolve; rw [zero_smul,add_zero]; rfl
lemma tilt_templates (hz:1/2≤R)(hM:Inputs P' H ((pink K.penalty w).acts f) (C.acts c))(hF:Gets F)(h: Marvel n U) (o:Site c)(φ:Exam D):
    let T:= P'; let k:=X.forest T.ratio; let M:=riseM T G k H; let Γ:=FreeResolvent.covariance G T k (pink K.penalty w)
    let w' p i := recitalP (U 0 i) (T.ratio.assemble (o,p)) (haloPull p φ)
    recitalP (filament P K w σ i X F (some c) U n d 0 r) o φ= twistV M (∑ p : Site T.ratio.count, increase P.L d • harvestL Γ (w' p) n r) := by
  intro T k M Γ w'
  letI : DecidableEq (Park G P.L):= by unfold Park Fink; infer_instance
  let V:=awakening i P σ K.penalty F; let N:= conditionalCov G X K w; let W:= veiled N
  let A :=scan (coarseMean G X K w); let B: Matrix (Co f (Loc G 1)) (Co c (Park G P.L)) ℝ := loomArc (G:=G) T.ratio; have he:= (conditional_truth G X K w hp).1
  have ht: Whole A:= scan_whole ((he.prod ((probe_recites G P K).1.flipped)).weight _)
  have hv: Gets V:=Gets_awake P σ K i hF
  have hu: B * A.acts c= M := by
    apply matrix_eq; intro v; rw [← Matrix.mulVec_mulVec]
    exact (loom_tip T.ratio (A.acts c *ᵥ v)).trans ((congr_arg (fineL G T.ratio) (tree_lodge G K (X:=X) s hp v hM)).trans (lodge_f ..))
  let E:= cream d U P.L; let u:=increase P.L d; have hx: ∀ i j,Tidy (E i j):= (creamy d P.L h.cap (fun i j=>(h.hem i j).pens) hz P.odd_side).2
  have hq (p): stitch (plug φ R ∘ E 0 p) c o=∑ j : Site T.ratio.count, u • twistV B (w' j p) := sewn_rune T.ratio hz h P.odd_side o φ
  rw [show recitalP (filament P K w σ i X F (some c) U n d 0 r) o φ=_ from fil_layer (F:=A) (K:=W) (r:=r) hx (veiled_whole he) ht hv n o φ]; simp_rw [hq]
  let f (p : Site T.ratio.count)(r:ℕ):= twistV B (w' p r)
  refine Eq.trans (congr_arg (twistV (A.acts c)) (h_collect (W.acts c) (fun j:Site T.ratio.count=> u • f j) univ n r)) ?_; rw [twist_for, twist_for]
  simp_rw [h_cost]; apply sum_congr rfl; intro b _; unfold f
  rw [harvest_swap,twist_cost,twist_cost,twist_join,show B*W.acts c*Bᵀ=Γ from salute s hp X w,hu]

omit hp in
private lemma shucks [Fintype A] [DecidableEq A] {M:Matrix A A ℝ} {V:CupA A r} (h:CoastT M V): twistV M V=V:= by
  ext1 v; let X (s:Finset (Fin r)) (i:Fin r) := if i∈s then M *ᵥ v i else v i
  have hx (s:Finset (Fin r)) : V (X s)=V v:= by
    induction s using Finset.induction_on with
    | empty=> simp_rw [X, Finset.notMem_empty,if_false]
    | insert i s hi ih=>
      have he : update (X s) i (v i)=X s := by funext j; by_cases hx:j=i <;> simp [X,hx,hi]
      have hh:= h i (X s) (v i)
      rw [he] at hh; rw [show X (insert i s)=update (X s) i (M*ᵥ v i) from (by funext j; by_cases hz:j=i <;> simp [X,hz]),hh,ih]
  rw [twists,show (fun i=> M *ᵥ v i)=X univ from (by funext i; simp [X])]; exact hx _
lemma shoresup (hz:1/2≤R)(hn:4 ≤ ℓ)(hm:Even c.val)(hX: Inputs P' H ((pink K.penalty w).acts f) ((pink K.penalty v).acts c))(hF: Gets F)(h: Marvel n U)(hL:∀ i,Polished (U 0 i)) (o:Site c)(φ:Exam D) :
    let g:=(linked P K c f s).ratio; let Y:= plaza G K.penalty v (some c); let V:= filament P K w σ i X F (some c) U n d
    let Z:= plaza G K.penalty w (some f)
    recitalP (frisk Y (V 0) n r) o φ=∑ p: Site P.L,increase P.L d • twistV (patron G H)
       (recitalP (frisk Z (U 0) n r) (g.assemble (o,p)) (haloPull p φ)) := by
  intro g Y V Z; let k:=K.penalty; let T:= X.forest g; let M:=riseM P' G T H; let N:=patron G H
  let D:=tensor G (bedtime k v c); let D':= tensor G (bedtime k w f); let Q:=FreeResolvent.covariance G P' T (pink k w)
  let S (p: Site P.L) j:= recitalP (U 0 j) (g.assemble (o,p)) (haloPull p φ)
  let F' (i:ℕ):= recitalP (V 0 i) o φ; let x:= increase P.L d
  have hs : Even f.val := s ▸ hm.mul_right _
  obtain ⟨_,_,hP⟩ := portion G K.penalty_pos hn
  obtain ⟨_,_,hQ⟩:= portion G K.penalty_pos P.order_cut
  have hh : ∀ i j,Tidy (V i j):=((period_flights hp hz h.hem h.cap hF).1 _).2
  have heq p : F' p= twistV M (∑ i:Site P.L,x • harvestL Q (S i) n p) := tilt_templates σ i s hp hz hX hF h o φ
  let H' i r:= harvestL Q (S i) n r
  have he (p r) : (x • H' p : Cupboard _ ) r=x • harvestL Q (S p) n r:=rfl
  rw [show recitalP (frisk Y (V 0) n r) o φ=harvestL D F' n r from earns D o ((hP v).2 _ hm) (fun _ _ => plaza_m ..) (hh 0) (plug φ R) n r,funext heq,harvest_swap]
  erw [show harvestL (M*D*Mᵀ) _ n r=∑ i:Site P.L,harvestL (M*D*Mᵀ) (x • H' i) n r from h_collect (M*D*Mᵀ) (fun i=> x • H' i) ..,twist_for]
  apply sum_congr rfl; intro p _; let o':Site f:= g.assemble (o,p); let R':= haloPull p φ; let C:= S p
  rw [h_cost,twist_cost,show recitalP (frisk Z (U 0) n r) (g.assemble (o,p)) _=harvestL D' C n r from earns D' o' ((hQ w).2 _ hs) (fun _ _ => plaza_m ..) (h.hem 0) (plug R' R) n r]; congr 1 -- scalar
  have ht' : ∀ i,Tensor.Sym (C i):= fun i=> (Tidy.map _ (h.hem 0 i)).sym _
  have hy : Ceils C n:= by
    intro i hi; unfold C S; rw [not_ne_iff.mp (mt (h.cap 0 i) (by omega)), recitalP,show plug R' R ∘ (0:EnvelopeU _ _ G i)=(0:Shale _ _) from funext fun _=>map_zero _,st_zero]
  unfold H' C; change twistV M (harvestL (M*D*Mᵀ) (harvestL Q C n) n r)= twistV N (harvestL D' C n r)
  let R0:= M*D*Mᵀ+Q; let Ψ:= tensor G (Precision.K ((pink k w).acts f)); let μ:= D'*Ψ
  have hT:=dwell (S:=P') G T K.penalty_pos P.order_cut hn (forest_precision G K w c f s hp T) hX
  change Ψ*(D'-R0)*Ψ=0 at hT
  have hE: Ψ*R0*Ψ=Ψ*D'*Ψ:= Eq.symm (sub_eq_zero.mp (by rw [Matrix.mul_sub,Matrix.sub_mul] at hT; exact hT))
  have hx : μ*R0*μᵀ=μ*D'*μᵀ := by
    have ht : Ψᵀ=Ψ := by unfold Ψ; rw [tensor_transpose,k_symmetric (heart_inverse _ K.penalty_pos P.order_cut w f).2.1]
    have hh (L0 : Matrix (Lines G f 1) (Lines G f 1) ℝ): μ*L0*μᵀ=D'*(Ψ*L0*Ψ)*D'ᵀ:= by unfold μ; rw [transpose_mul,ht]; simp only [Matrix.mul_assoc]
    rw [hh R0,hE, ← hh D']
  have hμ i: CoastT μ (C i):= fun j p x=> Sober.static K.penalty_pos P.order_cut (sober_vetted h).lucid (hL i) f R' j w o' x p
  have hh : harvestL (M*D*Mᵀ) (H' p) n r=harvestL D' C n r:= (stair_merge (M*D*Mᵀ) Q C ht' hy).symm.trans (sum_congr rfl fun i _=> terraces_equal hx C hμ ..)
  rw [show harvestL _ _ n r= _ from hh]
  have hz' : twistV μ (harvestL D' C n r)=harvestL D' C n r:= by
    apply shucks; intro i w v
    unfold harvestL; rw [_root_.sum_apply,_root_.sum_apply]; exact sum_congr rfl fun j _=> terraces_stay _ _ hμ j r i w v
  have hU : μ*M= μ*N:= by
    have hk : Ψ*M=Ψ*N:= by
      unfold M riseM N Ψ
      rw [tensor_same,tensor_same, ← tensor_times,← tensor_times, extracted, Matrix.mul_add,← Matrix.mul_assoc _ (Exterior.d 0 f),K_kills,Matrix.zero_mul,add_zero]
    unfold μ; rw [Matrix.mul_assoc _ _ M, Matrix.mul_assoc _ _ N,hk]
  nth_rw 1 [← hz']; rw [twist_join,hU,← twist_join,hz']
end YM.RG08.Pivot
