import YM.RG08.Spin.Flash
/-!
# Frame alphabet scope exact (not EOM quotient). Use actual Family Frames coherently.
Projection restricts also on polynomial probes of larger horizon.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Arcade
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier Place Scores.Pages Drift Spin
open WardBin
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}
section
variable (F: Labels.Frames G)(h:d ≤ j)
lemma marksUp (i : (F.level d).Index) : ∃ i', (F.level j).basis i'=raiseLabel G h ((F.level d).basis i) := by
   induction h with
   | refl=>exact ⟨i,rfl⟩
   | step h ih=>
     rename_i n; obtain ⟨k,hk⟩:= ih; obtain ⟨i',h'⟩:= F.coherent n (show _∈_ from Set.mem_range_self k)
     refine ⟨i',?_⟩; rw [h']; unfold Function.comp; rw [hk]; rfl

def sequel (i:(F.level d).Index):= (marksUp F h i).choose
lemma lifted (i): (F.level j).basis (sequel F h i)=raiseLabel G h ((F.level d).basis i) := (marksUp F h i).choose_spec
lemma sq_inj : Injective (sequel F h):= by
   intro i k hi; apply (F.level d).basis.injective; apply (show Injective (raiseLabel G h) from Submodule.inclusion_injective _)
   rw [show _= _ from (lifted F h i).symm,show _= _ from (lifted F h k).symm]; rw [hi]
lemma relayV (i): (F.level j).grades (sequel F h i)=(F.level d).grades i:= by
   apply pure_unique (Module.Basis.ne_zero ((F.level j).basis) (sequel F h i)) _ _ ((F.level j).pure _); rw [lifted]; exact (F.level d).pure _
lemma earned_coord (p: Label G d)(i): (F.level j).coords (raiseLabel G h p) (sequel F h i)=(F.level d).coords p i:= by
   conv_lhs=> rw [← (F.level d).basis.sum_repr p,map_sum,map_sum,Finset.sum_apply]
   rw [Finset.sum_eq_single i]
   · simp only [map_smul, ← lifted, Labels.Frame.coords_basis, Pi.smul_apply, Pi.single_eq_same,smul_eq_mul,mul_one]; rfl
   · intro b _ hb; simp only [map_smul, ← lifted, Labels.Frame.coords_basis, Pi.smul_apply,Pi.single_eq_of_ne ((sq_inj F h).ne hb.symm),smul_zero]
   simp

def this_letter (i:Letter (F.level d)) : Letter (F.level j) := ⟨sequel F h i.label,i.test,by rw [relayV]; exact i.bill.trans h⟩
lemma slotUP (i:Letter (F.level d)): slot (this_letter F h i)= slot i := congr_arg Prod.snd (relayV F h i.label)
lemma feeUP (i:Letter (F.level d)): fee (this_letter F h i)=fee i:= congr_arg (fun p:ℕ×ℕ=> p.1+cashT i.test) (relayV F h i.label)
lemma seat_inj : Injective (this_letter F h):= by
    rintro ⟨i,g,h₁⟩ ⟨v,p,h₂⟩ H; have hp:= congr_arg Letter.test H; have hA : sequel F h i=sequel F h v:= congr_arg Letter.label H; simp [sq_inj F h hA, show g=p from hp]
end
section tilt
-- Truncate using SAME linear radial coordinates

def linksH (G:Gauge)(d j:ℕ): Snap G d→L[ℝ] Snap G j := LinearMap.toContinuousLinearMap {
    toFun v:= trunk j (Drops.expand d v)
    map_add' p q:= by ext1 i; by_cases hv : i.val < d-1 <;> simp [Drops.expand,trunk,hv]
    map_smul' z v:= by ext1 i; by_cases hv: i.val < d-1 <;> simp [Drops.expand,trunk,hv]
  }
lemma expandsH (hp:d≤j)(v:Snap G d) : Drops.expand j (linksH G d j v)=Drops.expand d v:= by
    ext1 i; by_cases ht : i<j-1
    · rw [Drops.expand,dif_pos ht]; rfl
    have hh : ¬i<d-1:= by omega
    simp [Drops.expand,ht,hh]
lemma connectionH (hp:d ≤ j)(v:Snap G d)(i:Edge Cover)(t x:ℝ): partConnection j (Drops.expand j (linksH G d j v)) x i t=partConnection d (Drops.expand d v) x i t := by
    rw [expandsH hp]; unfold partConnection Source.potential; apply congr_arg (x • ·); exact Eq.symm (Finset.sum_subset (range_mono (by omega)) (fun i _ ht=> by rw [Drops.expand,dif_neg (mt mem_range.mpr ht)]; rfl)) -- not rfl?
lemma screen_more (H:Hol G)(d j : ℕ)(h:d≤j)(i:Fare G) : screenR G d i= screenR G j i ∘linksH G d j := by
    funext v; rw [Function.comp_apply, Vale.starts _ _ H,Vale.starts _ _ H]; apply congr_arg (scent i.2.2); apply congr_arg (G.plog ∘ G.mat); let x:= Drops.expand d v; let p:= linksH G d j v; let y:=Vale.heap i
    have hh := H.solves j (Drops.expand j p) 1 y
    rw [funext (connectionH h v y · 1)] at hh -- arrow order
    exact congr_fun ((H.solves d x 1 y).unique hh) 1
lemma cash_le (V:Shale (Loc G 1) r)(hv:Tidy V)(hp:Polished V)(H:Hol G) (hp': d ≤ j) (x: Fin k→ Snap G d) :
   amount V d k x=amount V j k ((linksH G d j) ∘ x) := by
    rw [penny_amt hv hp, penny_amt hv hp]; refine Finset.sum_congr rfl fun i _=>?_; unfold Vale.penny
    apply congr_arg ((i.length.factorial:ℝ)*·); apply congr_arg (wallet (grant i.length V)); funext u v
    have he (k : ℕ): ContDiffAt ℝ k (screenR G j v) 0:= by unfold screenR; apply ContDiffAt.of_le _ (show (k:WithTop ℕ∞) ≤ ω from le_top); exact ((scent _).contDiff.contDiffAt.comp _ (Film.lane_smooth ..))
    let K:=i.partSize u
    have hh : iteratedFDeriv ℝ K (screenR G d v) 0 (x ∘ i.emb u)=iteratedFDeriv ℝ K _ 0 ((linksH G d j) ∘ x ∘ i.emb u) := (DFunLike.congr_fun (congr_arg (fun f:Snap G d→ℝ=> iteratedFDeriv ℝ K f 0) (screen_more H d j hp' v)) (x∘ i.emb u)).trans (DFunLike.congr_fun (Next.Foundations.jets_linear (linksH G d j) (he _)) (x∘ i.emb u))
    exact hh
end tilt
end YM.RG08.Arcade
