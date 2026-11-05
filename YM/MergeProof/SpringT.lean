import YM.MergeProof.ChaletS
import YM.MergeProof.Paddle
import YM.MergeProof.Velvet

/-! deliver w from H. Base period arity width. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories Ac Bid Local
open Planned.GuardedAtom Accent Menu PhysicalNext.Repeat.Lotus Motion Extra.Multi
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V}{G:Gauge}{F J:Side}
variable (A:History G) (T:Hol G) (W:Bid.Worth)(φ ψ ζ u δ:ℕ→ℝ)(r:ℕ→ℕ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)) (p N k:ℕ)
set_option quotPrecheck false
local notation "R"=> A.rep N p
local notation "P"=> A.levels.budget
local notation "Γ"=> (fun m=>(A.levels.params m).columns)
-- uniform d for now.
variable {d:ℕ}{F:Labels.Frame G d}(S:SectionData F)(M:Extra.Histories.Music F A N p)
    (a:V→Motion)(v:V→F.Coeff) (o:∀ m:ℕ,V→Site (A.S.side m p))(w:V→ℝ)
    (Y:Config G (A.S.side N p)→Poly B)
    {q:∀ m:ℕ,m≤N → Config G (A.S.side m p)→Poly B}
-- rollback user affordability r≥0 relative bearing. deterministic outputs center anchor. 
structure Cherry (d k:ℕ) (A:History G)(φ ζ:ℕ→ℝ):Prop where
    level m : k ≤ m → φ m ≤ 1
    cost m : k ≤ m → φ m * (((A.S.block m).val:ℝ)^d*(A.levels.params (m+1)).columns)*ζ m ≤ ζ (m+1)
-- pin tapes
local notation "Ω"=> (fun m i=>soarK A N p M (v i) (a i) (fun m=>o m i) m)
local notation "θ"=> (fun m i=>soarF A S N p M (v i) (a i) (fun m=>o m i) m)
local notation "U'"=> (fun i:V=> stepUp (a i) (o N i) (initial S A N p (v i) 0))
local notation "w'"=> march w φ k
-- budget top.Back.Ext
lemma pollinate (h:A.Selected)(hQ:roomCost A.levels W)(hB:Bank W A.levels) (hk:k≤ N)(hw:∀ i,0<w i)(he:S.Sound T)(hh:Sung S A N p T W k M)
    (hi:Brine A k δ φ)(hx:Cherry d k A φ ζ)(hr:Monotone r)(hz:Occupancy (o k) (r k))(hM:Migrating A k p N o) (hS:Drake B (P k).B (o k)) (hl:Moonlit A r δ u D) {C:ℝ}
    (hC:Fiesta A F ζ ψ k)(ht:Banks A F C u ζ N)(hy:∀ i, w i*bond A N p M k (v i) ≤ ζ k) (hX: coverNumber (P N).B (S.footprint (0:Site (A.S.side N p))) ≤ 1) (hV:∀ (i:F.Index)(U:Config G (A.S.side N p)), ‖S.places (Size.axis F i) 0 U‖ ≤ C)
    (hg:∀ m:ℕ,k ≤ m→∀ hm:m<N, Carol S A N p m (D N p m hm) (M.tone (m+1)) (M.tone m) (ψ m))
    (hF:∀ x,profile (R N).activities ((M.tone N).plays x).forced=hook (R N).activities (R N).p.threshold (booster S (R N) 0 x))
    (ht':∀ m:ℕ,k ≤ m→∀ hm:m<N, q m hm.le=(A.levels.clock.op m p).push ((A.rep N p (m+1)).beta) (q (m+1) hm))
    (hp:q N le_rfl=birth B (A.rep N p N) U') (hP: Integrable (q N le_rfl) (prior G _)) : ∀ m:ℕ,k ≤ m → ∀ hm:m≤N, Served (R m) (θ m) (Ω m) (q m hm) (o m) (w' m) (topPitch A N m) 1 :=by
   have hm:= desal A r k p N δ φ o w hw hi B hM hS hr hz; have hW:=marines k φ w hw
   have h'(i m)(h:k ≤ m)(hp:m<N): w' (m+1) i=φ m*w' m i:=by simp only [march,if_pos h]
   have hD(j:V): ∃ g:∀ m:ℕ,ℕ → Config G (A.S.side m p)→ℂ, Wild A u k N p (fun m=>o m j) (fun m=>w' m j) (fun m=>θ m j) g (U' j) D ∧ ∀ i,k ≤ i→ i≤N→ profile (R i).activities (g i)=Ω i j := by
      let f m:=w' m j; have hu(i)(hc:k ≤ i)(hp:i≤N):0 < f i:= hm.pos _ hc hp j
      apply sweet A T S W ζ u ψ C k N p M (v j) (a j) (fun m=>o m j) f D h he hh hu ?_ ?_ hC ht hX hV ?_ (hF _) ?_
      · intro i h hp; unfold f; rw [h' j i h hp]; exact mul_le_of_le_one_left (hu i h hp.le|>.le) (hx.level i h)
      · apply cost_chain A T S W ζ k N p M (v j) f le_rfl (fun i h hp=> (hu i h hp).le) hk (fun i h hi=>?_) (fun i h hp=> hu i h hp.le) hQ hB hh
        · simpa only [f,hW] using! (hy j)
        simp only [f,h' j i h hi]; exact le_trans (le_of_eq (b:=φ i* (((A.S.block i).val:ℝ)^d * Γ (i+1))*ζ i*f i) (by unfold f; ring)) (mul_le_mul_of_nonneg_right (hx.cost i h) ((hu i h hi.le).le))
      · intro i he hm; exact congr_fun (hM.mare i he hm).symm j
      intro i he hp; obtain ⟨y,w,h,-⟩:= hl.days N p i hp; exact ⟨hg i he hp,h.propagate⟩
   choose g hg' hU using hD
   let G' i (j:V):= g j i
   have hν(j:V):Nectar A u D p N k o (w') θ G' U' j:=by
       obtain ⟨h1,h2,h3,h4,h5⟩:=hg' j; exact ⟨h1,h2,h3,h4,h5⟩
   intro i hi he
   have ht':= Accent.sentry A r δ u D p N o (w') θ G' U' h hk hm hl hν ht' hp hP i hi he|>.2.2
   have hq:tapes A p N G' i=Ω i:= funext fun j=> hU j i hi he
   rw [hq] at ht'; exact ht'
end YM.MergeProof
