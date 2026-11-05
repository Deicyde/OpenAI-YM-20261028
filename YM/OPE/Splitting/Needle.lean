import YM.OPE.Splitting.Basis
/-!
# Successive coherence: subtract the true projection

Our prescription doesn't require increasing the detector collars with r.
Instead of fitting grade-by-grade independent *splittings*, choose successive
bases in exact kernels of old point readouts. Their continuations are still
finite readouts. Implements actual filtering inclusions, not reference-slot
inclusions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prescription
open Function Matrix Table Finset
open scoped Topology BigOperators Classical ContDiff
variable {G: Gauge}{L:Register G}{S:Table L}{P:DiffPlan S}{m n : ℕ}
variable {U V:Prescription P}

def slice (P:DiffPlan S)(n:ℕ) : Qname P n↪ Mode P := ⟨Sigma.mk n,fun _ _ h=>eq_of_heq (Sigma.mk.inj h).2⟩
def tier (P:DiffPlan S)(n:ℕ):= Finset.univ.map (slice P n)
lemma mem_tier (x : Mode P) : x ∈ tier P n ↔ x.fst=n:= by
    rw [tier,mem_map]; constructor
    · rintro ⟨v,-,rfl⟩; rfl
    obtain ⟨i,x⟩:=x; rintro rfl; exact ⟨x,mem_univ _,rfl⟩
lemma band_zero (P:DiffPlan S): bands P 0=tier P 0:= Finset.ext fun x=> by rw [full_bands, Nat.le_zero,mem_tier]
lemma band_next (P:DiffPlan S)(n:ℕ): bands P (n+1)=bands P n∪ tier P (n+1):= Finset.ext fun x=>by rw [mem_union,mem_tier,full_bands,full_bands]; omega
lemma tier_far (P:DiffPlan S)(n:ℕ): Disjoint (bands P n) (tier P (n+1)):= Finset.disjoint_left.mpr fun _ hp hx=> by have h:=(full_bands ..).1 hp; have he :=(mem_tier ..).1 hx; omega
-- disjoint binder orientation
lemma tier_inside (i:Qname P n)(hm:n≤ m): slice P n i ∈ bands P m:= (full_bands ..).mpr hm
-- set grade
def edit (P: DiffPlan S) (n:ℕ) (U:Prescription P) (f: Qname P n→ S.Field n) (p:Qname P n→ Exterior L →₀ ℂ) : Prescription P where
    needle := fun ⟨i,t⟩=> update (β:= fun i=> Qname P i→ S.Field i) (fun i c=> U.needle (slice P i c)) n f i t
    sheet := fun ⟨i,t⟩=> update (β:= fun i=> Qname P i→ Exterior L →₀ ℂ) (fun i c=> U.sheet (slice P i c)) n p i t
lemma edited (U : Prescription P) (u t) : ∀ i,(edit P n U u t).needle (slice P n i) = (u i:S.Field n) ∧ (edit P n U u t).sheet (slice P n i)=t i:=by
    intro i; constructor <;> simp only [edit,slice,Function.Embedding.coeFn_mk,Function.update_self]
lemma edit_ext (U:Prescription P)(u t) (h:m<n) : Extends m U (edit P n U u t):=by
    constructor <;> (rintro ⟨k,i⟩ he; have hp:k≠n:= ((show k≤ m from (full_bands ..).1 he).trans_lt h).ne; simp only [edit,hp, ne_eq, not_false_eq_true,Function.update_of_ne] <;> rfl)

lemma Extends.atField (h:Extends n U V)(i: Mode P)(he:i∈bands P n)(d) : U.loaded i d=V.loaded i d:=by rw [loaded,loaded]; split; rw [h.needle i he]; rfl
lemma Extends.atTest (h:Extends n U V)(i: Mode P)(he:i∈ bands P n)(d): U.test i d=V.test i d:=by rw [test,test,h.sheet _ he]

variable (h:S.Symmetric)(hp:P.Inclusions S)
include h hp
lemma startRows : ∃ V:Prescription P, SignedOff 0 V :=by
    let q := ((old P 0).quotEquivOfEqBot (by rfl)); let E:Module.Basis (Qname P 0) ℂ (S.Field 0):= (quotientFrame P 0).map q
    choose B hB using fun i=> reachReads _ (E.coord i); let U:Prescription P:= ⟨fun _=>0,fun _=>0⟩; let V:= edit P 0 U E B
    have he:=edited U E B; have hb i: V.test (slice P 0 i) 0= E.coord i:=by unfold V test; rw [(he i).2]; exact hB i -- equality problem?
    have ht i: V.loaded (slice P 0 i) 0= E i:=by rw [cost V _ (tier_inside i le_rfl)]; change P.rise (le_refl 0) (V.needle (slice P 0 i)) = _; rw [P.arrival h hp,(he i).1]
    refine ⟨V,fun i j hi hj=>?_,fun x=>?_⟩
    · rw [band_zero] at hi hj; obtain ⟨i,-,rfl⟩:= mem_map.mp hi; obtain ⟨j,-,rfl⟩:= mem_map.mp hj; rw [hb,ht]; simp only [(slice P 0).injective.eq_iff]; by_cases hp:i=j
      · subst j; simp
      simp [hp]
    rw [band_zero,tier,sum_map]; simp_rw [hb,ht]; exact E.sum_repr _

/-- Keep all polarizers at old grades; one new ring of tests actualizes the
coordinate readouts of the next quotient. -/
lemma nextRows (U: Prescription P) (hu:SignedOff n U) : ∃ V: Prescription P, Extends n U V ∧ SignedOff (n+1) V:=by
    let ξ:= bands P n; let L':=old P (n+1); let R:= P.rise (Nat.le_succ n); let q:= L'.mkQ
    let A(i : Mode P) := U.test i (n+1); let p(i: Mode P):= U.loaded i n
    let B : S.Field (n+1)→ₗ[ℂ] S.Field n := ∑ i∈ξ,(A i).smulRight (p i)
    have hη(x): B x=∑ i∈ξ, A i x • p i:= by simp [B]
    have hb : LeftInverse B R := fun x=> by rw [hη]; unfold R A; simp_rw [U.affinity h hp]; exact hu.rebuilds x
    have hR(x): q (R x)=0:= (Submodule.Quotient.mk_eq_zero _).mpr ((show R x∈ LinearMap.range R from ⟨x,rfl⟩): R x∈ L')
    obtain ⟨S',hS⟩:= q.exists_rightInverse_of_surjective L'.range_mkQ
    let F : (S.Field (n+1) ⧸ L') →ₗ[ℂ] S.Field (n+1):= S'-R.comp (B.comp S')
    have ht : LeftInverse q F:=by intro x; unfold F; rw [LinearMap.sub_apply,LinearMap.comp_apply, map_sub,hR, sub_zero]; exact LinearMap.congr_fun hS _
    have hz x:B (F x)=0:=by unfold F; rw [LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.comp_apply, map_sub,hb _,sub_self]
    have hX (i) (hi:i∈ξ) (x): U.test i n (B x)= A i x:= by
       rw [hη,map_sum]; simp_rw [map_smul]; change (∑ j∈ξ, A j x*(U.test i n (p j))) = _; rw [sum_eq_single i]; simp [p,hu.bothWays i i hi hi]
       · intro j hj hs; simp [p,hu.bothWays i j hi hj, Ne.symm hs]
       tauto
    have hr x: x= F (q x) + R (B x):=by
       have hd:x-F (q x)∈L':= (Submodule.Quotient.mk_eq_zero _).mp (show q (x-F (q x))=0 by rw [map_sub,ht _,sub_self]); obtain ⟨a,he⟩:= (hd:x-F (q x)∈ LinearMap.range R)
       have he' : B x=a:= by rw [← hb a,he,map_sub,hz,sub_zero]
       rw [he',he]; abel
    let E : Module.Basis (Qname P (n+1)) ℂ (S.Field (n+1) ⧸ L'):= quotientFrame P (n+1); choose r ht' using fun i=> reachReads _ ((E.coord i).comp q); let V:= edit P (n+1) U (F ∘ E) r; have he:= edit_ext U (F ∘ E) r n.lt_succ_self
    have hV:=edited U (F ∘ E) r
    have hF(i): V.loaded (slice P (n+1) i) (n+1)= F (E i):= by rw [cost V _ (tier_inside i le_rfl)]; change P.rise (le_refl (n+1)) (V.needle (slice P (n+1) i)) = _; rw [P.arrival h hp,(hV i).1]; rfl
    have hY(i)(hi:i∈ξ): V.loaded i (n+1)= R (p i):= by rw [← he.atField i hi, U.load_next h hp i hi n.le_succ]
    have hc(i): V.test (slice P (n+1) i) (n+1)= (E.coord i).comp q:=by unfold test; rw [(hV i).2]; apply ht' i
    have hd(i)(hi:i ∈ ξ): V.test i (n+1)= A i:= (he.atTest i hi _).symm
    have hf (i) (hi:i∈ξ) (j:Qname P (n+1)): i≠ slice P (n+1) j:=fun h=> by have he:=(full_bands ..).1 hi; rw [h] at he; exact Nat.not_succ_le_self _ he
    refine ⟨V,he,fun i j hi hj=>?_,fun x=>?_⟩
    · simp only [band_next,mem_union,tier,mem_map,mem_univ,true_and] at hi hj; rcases hi with hi|⟨i,rfl⟩ <;> rcases hj with hj|⟨j,rfl⟩
      · rw [hd _ hi,hY _ hj]; unfold A R p; rw [U.affinity h hp,hu.bothWays i j hi hj] -- p unfold
      · rw [hd _ hi,hF j, if_neg (hf _ hi _), ← hX _ hi, hz, map_zero]
      · rw [hc i,hY _ hj,LinearMap.comp_apply,hR,map_zero,if_neg ((hf _ hj i).symm)] -- .symm ?
      rw [hc i,hF j, LinearMap.comp_apply,ht _]; simp only [(slice P (n+1)).injective.eq_iff]; by_cases h:i=j; subst i; · simp
      simp [h]
    rw [band_next,sum_union (tier_far ..),tier,sum_map]
    simp_rw [hF,hc]; have hi : ∑ i∈ξ,V.test i (n+1) x • V.loaded i (n+1) = R (B x):=by rw [hη,map_sum]; exact sum_congr rfl fun i hi=> by rw [hd i hi,hY i hi,map_smul]
    rw [hi]; change R (B x)+ (∑ i, E.repr (q x) i • F (E i)) = _; simp_rw [← F.map_smul]; rw [← map_sum,E.sum_repr,add_comm,← hr]
end YM.OPE.Prescription
