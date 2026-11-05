import YM.MergeProof.North.Prax



set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories  Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge} {n:Side} (C:Family G) (J j m p k N d:ℕ) {r:ℕ→ℕ}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "V'"=> Site (C.side J p)
local notation "Q"=> (hands C p J)
local notation "ξ"=> Mix.camp C p J
variable (a:Site (C.side j p))
local notation "o"=> bites C J j p a
local notation "v"=> loops C j p a
local notation "P"=> C.path.levels.budget
local notation "t"=> ((C.path.levels.budget k).B)
lemma gap_comp {δ φ:ℕ→ℝ} (h:Brine C.path k δ φ)(hk:k ≤ N): (P N).B^2 ≤ (C.S.toDepth hk p).count.val*t^2:=by
    induction hk with
    | refl=> change _ ≤ (C.S.steps k (k-k)).val * _; simp [Schedule.steps]
    | step hi ih=> rename_i i; have hp:= h.split i hi
                   let Z:= C.S.oneStep i p; rw [size_comp (C.S.toDepth hi p) Z, mul_assoc]; exact hp.trans (Nat.mul_le_mul_left Z.count.val ih)
lemma reachBit (hz:J≤k)(i:V')(b:Bool) : separation (o k (i,b)) (ξ k i) ≤ separation (v k) 0:=by
    cases b
    · rw [biteF,separation_self]; exact Nat.zero_le _
    unfold bites; let A:= affine (hands C p J i).1 (ξ k i); have ht : ξ k i=A 0:= by simp [A,affine]
    change separation (A (v k)) (ξ k i) ≤ _; rw [ht]; simp [A,affine,-Signed.act_zero, -zero_add,separation_signed,separation_translate]
lemma alreadyP {α X:ℕ} (hk:J ≤ k)(hp:α+1≤ separation (v k) 0)(hv:separation (v k) 0≤ X)(hX:α+1+2*X ≤ (C.S.toDepth hk p).count.val):∀ (i j':Name V'),i≠j'→ α+1 ≤ separation (o k i) (o k j'):=by
    rintro ⟨i,b⟩ ⟨j',c⟩ h; by_cases hi:i=j'; subst i
    · have hf:b ≠ c:=fun htq=> h (htq ▸ rfl); rw [bit C J j p k a hk j' b,bit C J j p k a hk j' c]; simp only [affine,separation_signed,separation_translate]; cases b <;> cases c; exact (hf rfl).elim
      · rw [biteT C J j p k a hk,biteF, zeroMama C J p k hk,separation_comm]; exact hp
      · rw [biteT C J j p k a hk,biteF, zeroMama C J p k hk]; exact hp
      exact (hf rfl).elim
    have ht:(C.S.toDepth hk p).count.val ≤ separation (ξ k i) (ξ k j'):=by simp_rw [elev C J p k hk,Station.both]; exact Nat.le_mul_of_pos_right _ (separation_pos _ _ hi)
    have hx:= reachBit C J j p k a hk i b; have hL:=reachBit C J j p k a hk j' c
    have h₁:=separation_triangle (ξ k i) (o k (i,b)) (o k (j',c)); have h₂:=separation_triangle (ξ k i) (o k (j',c)) (ξ k j'); rw [separation_comm _ (o k (i,b))] at h₁; omega
lemma vizier {X:ℕ} {δ φ:ℕ→ℝ} (h:Brine C.path k δ φ)(hk:J ≤ k)(hp:t^2+1≤ separation (v k) 0)(hv:separation (v k) 0 ≤ X)(hX:t^2+1+2*X ≤ (C.S.toDepth hk p).count.val):∀ i,k ≤ i→i≤j→ Edition.Spaced (P i).B (o i):=by
    have hY:=alreadyP C J j p k a hk hp hv hX; intro i hi he s u hΔ; have hh:=(bitesParent C J j p k a hk hi he)
    let T:= C.S.toDepth hi p; let L:=T.count.val; have hx(x): 2*separation (o i x) (T.embed (o k x))< L:=by rw [← hh]; exact midway T (C.S.toDepth_odd hi p) _
    have ht:L*(t^2+1) ≤ separation (T.embed (o k s)) (T.embed (o k u)):=by rw [Station.both]; exact Nat.mul_le_mul_left _ (hY s u hΔ)
    have hh₁:= separation_triangle (T.embed (o k s)) (o i s) (T.embed (o k u)); have hh₂:=separation_triangle (o i s) (o i u) (T.embed (o k u)); rw [separation_comm (T.embed (o k s)) (o i s)] at hh₁ -- which?
    have he':(P i).B^2 ≤ L*t^2:=gap_comp C p k i h hi; have hh₃:=hx s; have hh₄:=hx u; rw [mul_add,mul_one] at ht; omega
lemma coverB {d':ℕ}(he:J ≤ k)(hp:separation (v k) 0 ≤ d'*t): ∀ i:V',coverNumber t ({o k (i,false),o k (i,true)}:Support _) ≤ (2*d'+1)^4:=by
    intro i; have hh:= Corona.tile (o k (i,false)) d' t (P k|>.B_pos)
    refine (Corona.cover_mono (show ({o k (i,false),o k (i,true)}:Support _)⊆ halo (d'*t) {o k (i,false)} from ?_) t).trans ?_
    · intro x h; rcases mem_insert.mp h with h|h
      · rw [h]; exact halo_spec.mpr ⟨_,mem_singleton_self _,by rw [separation_self]; exact Nat.zero_le _⟩
      rw [mem_singleton.mp h]; refine halo_spec.mpr ⟨o k (i,false),mem_singleton_self _,?_⟩; rw [biteF, separation_comm]; exact (reachBit C J j p k a he i true).trans hp
    simpa only [two_mul] using hh
end
end YM.MergeProof.Ribbons
