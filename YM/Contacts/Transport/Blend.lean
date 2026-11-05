import YM.Contacts.Transport.Register
/-! # The mixed extension, ordinary correlations, one-field reading

Use this on forms in the full field space; outside the horizons the mixed map has an identical
continuation obtained by raising (same labels only). Equivariance respects these grade choices,
shown via the transport on each summand. Everything linear before integration; use finite sums
of the integrated (norm-controlled) per-grade terms on their apertures to test with mixed fields.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Transport
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Harvest Route Solstice Ordered
open scoped Topology Classical BigOperators ContDiff TensorProduct InnerProductSpace MeasureTheory
variable {E X : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {k : ℕ}{G:Gauge}{C:Family G}{Ord:Extraction.Order}{S:Table C.book}{Z:Final C Ord S}{d d': Fin k→ℕ}
local notation "V!" => Expression Z.sector.derivatives
local notation "GN" => Normal.Group k
abbrev entire (k:ℕ):Normal.Group k:= Finset.univ
abbrev VectorMap (d : Fin k→ℕ) (S:Table C.book)(X:Type)[AddCommMonoid X][Module ℂ X] := MultilinearMap ℂ (fun i=> S.Field (d i)) X
variable (M:Devices Z.sector.derivatives)(o:Points k)(P:E→ₗᵢ[ℝ] Points k)(s:ℝ)(Q:Pieces (entire k))

def assigned (d:Fin k→ℕ) : VectorMap d S (Score E (Expression Z.sector.derivatives)):= by
    let T : Cells S d → Score E (Expression Z.sector.derivatives):= fun f=> parcel ((waySystem P M o d f).full P s) Q
    have he(x:Cells S d)(i:Fin k) : GradeMap (fun t=> T (Function.update x i t)):= (across M o P s x i (entire k) Q).1 (Finset.mem_univ _)
    refine MultilinearMap.mk' T (fun x i y z=>?_) (fun x i c y=>?_)
    all_goals obtain ⟨t,ht⟩:=he x i; have hh u:T (Function.update x i u)= t u:= congr_fun ht u; simp_rw [hh]
    · exact map_add ..
    exact map_smul ..
-- finite split weight stage.
abbrev Dimensions (d : Fin k→ℕ) := (i:Fin k) → Fin (d i+1)
abbrev carriesN (v : Dimensions d) : Fin k→ℕ:= fun i=>(v i).val
def ensemble (d : Fin k→ℕ) (v : Dimensions d) : VectorMap d S (Score E (Expression Z.sector.derivatives)):= (assigned M o P s Q (carriesN v)).compLinearMap (fun i=>M.splitting.part (v i) (d i))
def blend (d : Fin k→ℕ) := ∑ v, ensemble M o P s Q d v
lemma blended (f : Cells S d): blend M o P s Q d f= ∑ v:Dimensions d, ensemble M o P s Q d v f:= by unfold blend; rw [_root_.sum_apply]
/-- already homogeneous and registered. -/
lemma pure_read {f : Cells S d}(h : basisCells M d f) : blend M o P s Q d f= parcel ((waySystem P M o d f).full P s) Q:= by
    let t:Dimensions d:=fun i=>Fin.last _; rw [blended,Finset.sum_eq_single_of_mem t (Finset.mem_univ t)];
    · change parcel ((waySystem P M o d (fun i=> M.splitting.part _ (d i) (f i))).full P s) _ =_; congr 2
      exact congrArg (waySystem P M o d) (funext fun i=> ((LinearMap.congr_fun (M.splitting.top_part (d i)) (f i)).trans (M.top_of_grade _ ⟨_,h i⟩)))
    intro v _ hv; obtain ⟨i,hi⟩:=Function.ne_iff.mp hv -- name
    refine MultilinearMap.map_coord_zero (assigned M o P s Q (carriesN v)) i (m:= fun i=>M.splitting.part (v i) (d i) (f i)) ?_
    have hx:(v i).val ≠ d i := fun he=> hi (Fin.ext he); rw [← show M.splitting.top (d i) (f i)= f i from M.top_of_grade (d i) ⟨f i,h i⟩]; exact LinearMap.congr_fun (M.splitting.part_top hx) _ -- comp pm

variable (h : ∀ i:Fin k,d i≤d' i)
def raise (f : Cells S d) : Cells S d' :=fun i=> Z.sector.derivatives.rise (h i) (f i)
def upgrades : Dimensions d ↪ Dimensions d' where
   toFun v i:=⟨(v i).val,by have he:=(v i).isLt; have ht:=h i; omega⟩
   inj' f g hh:=funext fun i=> Fin.ext (congr_arg (@Fin.val (d' i+1)) (congr_fun hh i))
-- original grade invariance
lemma higher {f : Cells S d}(v : Dimensions d) : ensemble M o P s Q d v f = ensemble M o P s Q d' (upgrades h v) (raise (Z:=Z) h f):= by
    apply congrArg (assigned M o P s Q (carriesN v)); funext i; exact (M.splitting.part_rise M.hierarchy.laws.toSymmetric M.incl (w:=(v i).val) (h i) (f i)).symm -- motives
lemma blended_up (f : Cells S d) : blend M o P s Q d f = blend M o P s Q d' (raise (Z:=Z) h f):= by
    rw [blended,blended]; let V:=(Finset.univ:Finset (Dimensions d)).map (upgrades h); let p(v:Dimensions d'):= ensemble M o P s Q d' v (raise (Z:=Z) h f); trans ∑ i∈V,p i
    · unfold V; rw [Finset.sum_map]; exact Finset.sum_congr rfl fun i _=> higher M o P s Q h i
    apply Finset.sum_subset (Finset.subset_univ _); intro v _ hh; have he : ¬∀ i,(v i).val < d i+1:= fun hE=> hh (Finset.mem_map.mpr ⟨fun i=>⟨(v i).val,hE i⟩,Finset.mem_univ _,funext fun i=>Fin.ext rfl⟩); push Not at he; obtain ⟨i,hi⟩:=he; apply (assigned M o P s Q (carriesN v)).map_coord_zero i
    change M.splitting.part _ _ (Z.sector.derivatives.rise (h i) (f i))=_; rw [M.splitting.part_rise M.hierarchy.laws.toSymmetric M.incl, M.splitting.beyondZero (show d i<(v i).val from hi),LinearMap.zero_apply]
lemma blended_image {f : Cells S d}(v : SmoothTests E) (x:E) : action x v (blend M o P s Q d f)= ∑ j:Dimensions d, localImage M P Q o s ( (fun i=> M.splitting.part (j i) (d i) (f i)): Cells S (carriesN j)) v x := by rw [blended,map_sum]; rfl

omit [FiniteDimensional ℝ E] in
lemma inside_conf {U : Set E} (h : ∀ x∈U,(P x+o)∈ conf k) : GroupsTest P (⊥:Pieces (entire k)) o U:= by
   have ht (i) (hi:i∈ (⊥:Pieces (entire k)).parts) : ∃ j,{j}=i := by obtain ⟨j,hj,rfl⟩:= Finpartition.mem_bot_iff.mp hi; exact ⟨j,rfl⟩
   constructor
   · intro i hi; obtain ⟨j,rfl⟩:=ht _ hi; rw [rank_eq_zero (by simp)]; exact bot_le
   · intro i hi; obtain ⟨j,rfl⟩:=ht _ hi; simp [Collapsed]; --
   intro x hx i hi j hj hh a ha b hb; obtain ⟨i,rfl⟩:=ht _ hi; obtain ⟨j,rfl⟩:=ht _ hj; rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]; exact Injective.ne (h x hx) (fun he=>hh (by rw [he]))
lemma singletons {g:GN}(i:GN) (h:i∈ (⊥:Pieces g).parts): i.card≤1:=by obtain ⟨i,hi,rfl⟩:=Finpartition.mem_bot_iff.mp h; simp

-- already same within basis assignments. On varying input labels by any changes use below continuity and this on mixed.
lemma harmonic (x:E)(p:SmoothTests E)(T:Cells S d) (hQ: GroupsTest P Q o (tsupport p.val))(h : ∀ x∈ tsupport p.val,(P x+o)∈ conf k) : localImage M P Q o s T p x=p.val x • ∏ i,insertField M.basis ((P x+o) i) (d i) (T i):= by
    unfold localImage; rw [overlap_action _ _ _ hQ (inside_conf o P h), at_singles _ (fun i hi=>singletons i hi), action_tmul,Finset.prod_apply]; rfl

omit [FiniteDimensional ℝ E] in -- variables not referenced below
lemma spokes (f : Cells S d)(x:E4)(j:Fin k) : ∑ i:Fin (d j+1), insertField M.basis x i (M.splitting.part i (d j) (f j))= insertField M.basis x (d j) (f j):= by
    nth_rw 2 [← M.splitting.recombine M.hierarchy.laws.toSymmetric M.incl (d j) (f j)]; rw [map_sum]; exact Finset.sum_congr rfl fun i _=> (insert_rise M.basis M.coherent M.hierarchy.laws.toSymmetric M.incl x (Nat.le_of_lt_succ i.isLt) _).symm
lemma one_image (T : Cells S d)(p : SmoothTests E)(hQ : GroupsTest P Q o (tsupport p.val))(h : ∀ x∈tsupport p.val,(P x+o)∈conf k)(x:E) : action x p (blend M o P s Q d T)= p.val x • fieldWord M.basis (P x+o).ofLp (fun i=> ⟨_, T i⟩):= by
    rw [blended_image]; simp_rw [harmonic _ _ _ _ _ _ _ _ hQ h, ← Finset.smul_sum]; unfold fieldWord; simp only; simp_rw [← spokes M T]; rw [Fintype.prod_sum] -- ok
lemma expected (T : Cells S d)(p : SmoothTests E)(θ:Viewers Z)(hQ:GroupsTest P Q o (tsupport p.val))(h : ∀ x∈tsupport p.val,(P x+o) ∈ conf k) (x:E) : readExpr M.basis (spectator Z θ) (action x p (blend M o P s Q d T))= p.val x*S.useAt (spectator Z θ) (P x+o) (fun i=> ⟨_, T i⟩):= by
   rw [one_image M o P s Q T p hQ h x,map_smul,read_fields M.basis M.coherent _ (spectate Z θ).laws.toSymmetric (spectate_respects Z _) (spectate_ready Z _)]; split; rfl; next hx=> rw [notMem_support.mp (show x∉ support p.val from fun hm=> hx (h x (subset_closure hm))),zero_mul,smul_zero]
end YM.Contacts.Transport
