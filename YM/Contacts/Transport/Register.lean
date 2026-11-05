import YM.Contacts.Transport.Tangent
import YM.Contacts.Transport.Orbit
/-!
# Grade registration & linear extension

Full family on homogeneous actual labels, including extending from real basis within each grade
and evaluating non-homogeneous finite combinations from those grades. Changing the ambient
filtration stage doesn't introduce extra field identities; always perform the blending with the
same splitting, and true counterterms in each term use the *original weight list*. Gives also a
simple proof of well-definedness of linear extension as score equality (no coincident instructions
when computing these conversions) and of raising the labels in it. Coordinate basis used here
includes the unit. Nothing about any identity involving removing the unit slot from a contact.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Transport
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Harvest Route Solstice Ordered
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E W I X : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {k : ℕ}{G:Gauge}{C:Family G}{Ord:Extraction.Order}{S:Table C.book}{Z:Final C Ord S}{d d': Fin k→ℕ}
local notation "V!" => Expression Z.sector.derivatives
local notation "GN" => Normal.Group k
variable (M : Devices Z.sector.derivatives)
-- real basis
private def conjGrade (n:ℕ)(p:M.splitting.stratum n) : M.splitting.stratum n:=
   ⟨S.conj M.hierarchy.spin n p, by cases n; exact Submodule.mem_top
                                    show _ ∈ LinearMap.ker _
                                    rw [LinearMap.mem_ker,← M.covariant.real, show M.splitting.down _ _=0 from p.property,map_zero]⟩
lemma turns_basis (s:Ortho)(b:Bool)(n:ℕ){t : S.Field n}(h:t∈M.splitting.stratum n) : M.rotation.act n s (Ribbon.glaze M b n t)∈ M.splitting.stratum n := by
   let c:M.splitting.stratum n:= ⟨t,h⟩; have he : Ribbon.glaze M b n t∈M.splitting.stratum n:=by cases b; exact h; exact (conjGrade M n c).property
   cases n; exact Submodule.mem_top
   show _∈ LinearMap.ker _; rw [LinearMap.mem_ker,← M.covariant.act, show M.splitting.down _ (Ribbon.glaze M b _ t)=0 from he,map_zero]
private def RealGrade (n:ℕ) := {x:M.splitting.stratum n | conjGrade M n x=x}
private lemma shadow (n : ℕ)(p:M.splitting.stratum n) : p∈ span ℂ (RealGrade M n):=by
   let q:=conjGrade M n p; let S':=span ℂ (RealGrade M n); have hh:=S.reflect_star M.hierarchy.spin n p.val
   have hp:p+q∈ S':= subset_span (show _ from ( ?_ : conjGrade M n (p+q)=p+q)); swap; · apply Subtype.ext; change S.conj _ _ (p.val+S.conj _ _ p.val)=p.val+_; rw [map_add,hh,add_comm]; rfl
   have ht:(Complex.I) • (p-q)∈ S':= subset_span (show _ from (?_ : conjGrade M n (_ • (p-q))= Complex.I • (p-q))); swap; · apply Subtype.ext; change S.conj _ _ ((Complex.I) • (p.val-S.conj _ _ p.val))= Complex.I • (p.val-_); rw [map_smulₛₗ,map_sub,hh]; simp [show (starRingEnd ℂ) Complex.I= -Complex.I from Complex.conj_I, smul_sub, q,conjGrade]; abel -- maybe
   have hc := S'.smul_mem (1/2:ℂ) (S'.add_mem hp (S'.smul_mem (-Complex.I) ht)); rw [smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul,show p+q+(p-q)=(2:ℂ) • p from by rw [two_smul]; abel, smul_smul,div_mul_cancel₀ _ (by norm_num), one_smul] at hc; exact hc
private lemma picked (n : ℕ) (S : Set (M.splitting.stratum n))(h : S ⊆ RealGrade M n)(hp : LinearIndepOn ℂ id S): ∃ (N:ℕ)(x:Module.Basis (Fin N) ℂ (M.splitting.stratum n)), S ⊆ range x ∧ range x ⊆ RealGrade M n := by
    obtain ⟨s,hs,hS,hm,he⟩:= exists_linearIndepOn_id_extension hp h; let b:Module.Basis s ℂ (M.splitting.stratum n):= Module.Basis.mk he.linearIndependent_restrict (by
       intro z _; have hsp:= span_le.mpr hm (shadow M n z); simpa using hsp); letI:Finite s:=Module.Finite.finite_basis b; letI:= Fintype.ofFinite s; let e:= Fintype.equivFin s
    have hL (x : s) : b x=x.val:= by simp [b]
    refine ⟨_,b.reindex e, fun p hp=> ⟨e ⟨p,hS hp⟩,by rw [Module.Basis.reindex_apply, e.symm_apply_apply]; exact hL _⟩,?_⟩
    rintro z ⟨i,rfl⟩; simpa only [Module.Basis.reindex_apply,hL] using hs (e.symm i|>.property)
/-- linear extension on these basis readings, first index in every read retains assignment d. -/
structure SystemBasis where
   N : ℕ→ℕ
   basis (n : ℕ) : Module.Basis (Fin (N n)) ℂ (M.splitting.stratum n)
   unit_row : ∃ i, (basis 0 i).val=S.unit 0
   pure (n : ℕ) : ∀ i, S.conj M.hierarchy.spin n (basis n i).val=(basis n i).val
lemma real_basis : Nonempty (SystemBasis M):= by
   let z: M.splitting.stratum 0:=⟨S.unit 0,Submodule.mem_top⟩
   have he:z≠0:= fun he=> S.alive 0 M.hierarchy.laws (congr_arg Subtype.val he); have hp:S.conj M.hierarchy.spin 0 (S.unit 0)=S.unit 0:=S.conj_unit ..
   obtain ⟨V,U,hz,h'⟩:=picked M 0 {z} (singleton_subset_iff.mpr (show _ from (show z∈ RealGrade M 0 from Subtype.ext hp))) ((linearIndepOn_singleton_iff ..).2 he)
   choose N B h hh using fun n:ℕ=> picked M (n+1) ∅ (by simp) (linearIndepOn_empty ..); let F (ℓ:ℕ):ℕ:= Nat.casesOn ℓ V N; let u(n:ℕ): Module.Basis (Fin (F n)) ℂ (M.splitting.stratum n) := Nat.casesOn (motive:=fun n=> Module.Basis (Fin (F n)) ℂ (M.splitting.stratum n)) n U B; -- 
   refine ⟨F,u,?_,fun n i=>?_⟩ -- Nonempty syntax?
   · obtain ⟨i,hi⟩:= hz (Set.mem_singleton z); exact ⟨i, congrArg Subtype.val hi⟩
   cases n with
   | zero=> exact congr_arg Subtype.val (h' (Set.mem_range_self i))
   | succ n=> exact congr_arg Subtype.val (hh n (Set.mem_range_self i))
end YM.Contacts.Transport
