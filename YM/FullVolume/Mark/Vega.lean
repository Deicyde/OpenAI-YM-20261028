import YM.FullVolume.Mark.Nursery
import YM.FullVolume.Mark.Wheels
/-! Generic deterministic step on given layout; Chronicle preserves payroll and graph. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Function Filter MeasureTheory Finset Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{B:SectionData F}{Y:Hol G}{H:History G}{N p m:ℕ}{u w v:ℝ}
variable {W:Worth}
section seam
variable (hw: roomCost H.levels W)(hk:Bank W H.levels)
variable {S: GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{X:Set Wing}{F':Heading F} (U: Tool F H N p m)(hf:Tool.Cap U B Y W S F' u v w X)(hA:Afford U.plate Y (H.rep N p (m+1)) (H.rep N p m)) {E:Desk G (H.S.side m p)} {D:Desk G (H.S.side (m+1) p)} (hu:Well (H.rep N p (m+1)) D (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))) (he:Well (H.rep N p m) E (Real.sqrt (H.levels.clock.forcedAllowance m)))
local notation "Q₀"=> tested U hf hA hu he hw hk
variable {P:Voice F H p (m+1)}{Q:Voice F H p m}
-- Recipe.Param. insists literal `pages`. proof param labels.
def Boasts (T:Tool F H N p m)(Q:Voice F H p m)(P:Voice F H p (m+1))(B: SectionData _)(Y:Hol G) {D:Desk G (H.S.side (m+1) p)}(hz:Well (H.rep N p (m+1)) D (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))) := ∀ h:Heard B H N p Y (m+1) P, ∀ x,Q.plays x=(measure h T.up hz).point T (P.index x) -- binder F shadow
variable (hC:Heard B H N p Y (m+1) P) (hr:Heard B H N p Y m Q) (h:Boasts U Q P B Y hu)
local notation "S₀"=> measure hr U.down he
local notation "S₁"=> measure hC U.up hu
include hf hw hk hA h hr hC
lemma lever (i:F.Coeff) : Q.index i=(Q₀).leanings S₁ (P.index i):=by
    rw [← hr.currents,h hC i]; rfl
lemma misses : S₀=(Q₀).flow S₁:=by
    let f:=(Q₀); let V:= S₁; let Z:= S₀
    have hx: Z.g=(f.flow V).g:=by
       refine LinearMap.ext fun x=>?_ ; obtain ⟨v,rfl⟩:= Q.index.surjective x
       apply Coin.noted
       have hh : Coin.uses (Z.g (Q.index v))=capture (Q.plays v) U.down:=by dsimp only [Z]; rw [notations,Q.index.symm_apply_apply]
       rw [hh,h hC v,lever hw hk U hf hA hu he hC hr h v]; change _= Coin.uses ((V.step U hf hu he hw hk).g (V.index U hf hu hw hk (P.index v))); rw [Gram.signs];rfl
    have he (A:ℝ) {E:Desk G (H.S.side m p)} (x y: Gram F Y E A)(he:x.g=y.g):x=y:=by cases x;cases y; simp only [Gram.mk.injEq]; exact he
    exact he _ _ _ hx
omit hA h hr
include hu
lemma sends (hr:Chorus H N p (m+1) P):∃ Z: Voice F H p m, (Heard B H N p Y m Z ∧ Responds B H N p W m P Z ∧ Carol B H N p m S P Z w ∧ Chorus H N p m Z ∧ Boasts U Z P B Y hu):=by
    obtain ⟨G,hQ,hg,hH,hU,hV⟩:= motor B H N p Y W m P hC hw hk F' S X U hf hr hu
    exact ⟨G,hg,hH,hV,hU,fun _=> hQ⟩
end seam
section compose
variable (W:Worth)
variable {S:∀ m,Desk G (H.S.side m p)} {Q:ℕ→ℝ}
-- buy P at arbitrary m with incoming (k-founded) masks independent of m<n.L. proof through Boot.T shell.
variable (k':ℕ)(D:∀ m,k' ≤ m → m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(U: ∀ m,k' ≤ m →m<N → Tool F H N p m)
variable (ζ:∀ m, k' ≤ m → ∀ _:m<N, Well (H.rep N p (m+1)) (S (m+1)) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
def Portal (B:SectionData F)(H:History G)(N p:ℕ)(Y:Hol G)(W:Worth)(k':ℕ)(D:∀ m,k' ≤ m → m < N → GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(Q:ℕ→ℝ) {S:∀ i,Desk G (H.S.side i p)} (ζ:∀ i,k' ≤ i → i<N → Well (H.rep N p (i+1)) (S (i+1)) (Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (U:∀ i,k' ≤ i →i<N → Tool F H N p i) (M:Extra.Histories.Music F H N p): Prop:= Sung B H N p Y W k' M∧∀ i:ℕ,∀ h:k' ≤ i,∀ he:i<N, Carol B H N p i (D i h he) (M.tone (i+1)) (M.tone i) (Q i)∧ Chorus H N p i (M.tone i)∧ Boasts (U i h he) (M.tone i) (M.tone (i+1)) B Y (ζ i h he)
set_option maxHeartbeats 440000 in
lemma composeT (hw:roomCost H.levels W)(hk:Bank W H.levels)(V:Voice F H p N)(hv: OnTop B H N p Y V)(hp: Chorus H N p N V)(h: k' ≤  N) (calls :∀ m,∀ h:k' ≤ m,∀ hm:m<N,∃ c v X R, Tool.Cap (U m h hm) B Y W (D m h hm) R c v (Q m) X ∧ Afford (U m h hm).plate Y (H.rep N p (m+1)) (H.rep N p m)):∃ M: Extra.Histories.Music F H N p, M.tone N=V∧ Portal B H N p Y W k' D Q ζ U M:=by
   induction h using Nat.decreasingInduction with
   | self=>
     let a (m : ℕ) : Voice F H p m := ⟨fun _ => Extra.Histories.primary 0 0, fun _ => 0,LinearEquiv.refl ℂ _⟩
     let M : Extra.Histories.Music F H N p := ⟨update a N V⟩
     have he : M.tone N=V := update_self N V a
     refine ⟨M,he,⟨he.symm ▸ hv, le_rfl, fun i hi ht => ?_, fun i hi ht => by omega⟩,fun i hi ht=> by omega⟩
     obtain rfl : i=N := le_antisymm ht hi
     rw [he]; exact hv.heard
   | of_succ k hk' ih=>
     obtain ⟨M,hM,hS,hD⟩:= ih (fun i hi hv=> D i (by omega) hv) (fun i hi hv=> U i (by omega) hv) (fun i hi hv=> ζ i (by omega) hv) (fun i hi hv=> calls i (by omega) hv)
     obtain ⟨c,v,X,R,hC,hf⟩:= calls k le_rfl hk'
     have hSq: Chorus H N p (k+1) (M.tone _):=by
        by_cases h:k+1=N
        · change Chorus H N p (k+1) (M.tone (k+1)); rw [h,hM]; exact hp
        exact (hD (k+1) le_rfl (by omega)).2.1
     obtain ⟨v,hV,hT,hX,hY,hJ⟩:= sends hw hk _ hC (ζ k le_rfl hk') (hS.earned _ le_rfl hk') hSq
     let t : Extra.Histories.Music F H N p := ⟨update M.tone k v⟩
     have hh : t.tone k=v := update_self k v M.tone
     have htr (i : ℕ) (hi : k < i) : t.tone i=M.tone i := update_of_ne hi.ne' v M.tone
     refine ⟨t,(htr N hk').trans hM,⟨?_,hk'.le, fun i hi he => ?_,fun i hi he => ?_⟩,fun i hi he=>?_⟩
     · rw [htr _ hk']; exact hS.head
     · obtain h|h := lt_or_eq_of_le hi
       · rw [htr _ h]; exact hS.earned i h he
       subst i; rw [hh]; exact hV
     · obtain h|h := lt_or_eq_of_le hi
       · rw [htr i h,htr (i+1) (by omega)]; exact hS.step i h he
       subst i; rw [htr (k+1) k.lt_succ_self,hh]; exact hT
     obtain hl|hl:= lt_or_eq_of_le hi
     · rw [htr i hl,htr (i+1) (by omega)]; exact hD i hl he
     subst i; rw [hh,htr (k+1) k.lt_succ_self]; exact ⟨hX,hY,hJ⟩
end compose
end YM.MergeProof.Matric
#print axioms YM.MergeProof.Matric.composeT
#print axioms YM.MergeProof.Matric.lever
#print axioms YM.MergeProof.Matric.misses
