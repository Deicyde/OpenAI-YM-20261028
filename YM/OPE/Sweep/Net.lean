import YM.OPE.Rough.Gate
import YM.OPE.Sweep.Join

/-!
# Regrouping net

`Collar` relates all copies, `Cross` purchases cross-cell separation;
under these hypotheses representatives may be chosen once, then
repeated in every cell with the same relative label. The groups from a
current net induction can fuse whenever necessary to maintain parent
separation, at most as many times as there are children. A single
step of halo price pays for *each* currently active anchor and its
next representative independently; no assumption that all children
are within a single halo.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Extra.Multi Push GridApprox.Nil Ac Pressure Corona Next.Rank Station Source Local Menu Extra.Histories PhysicalNext.Repeat
open scoped Topology BigOperators Classical
variable {G:Gauge}{n n':Side} {S:Schedule} {V I J : Type}[Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{A:History G}{E:V→Site n}{P:V→Motion}
  {v:V}{o:V×I→Site n} {b ℓ : ℕ}
variable (i:I)(hb:0<b)

include hb in
/-- Net with a distinguished representative. The surjection centers
are repeated, so all copies agree on the group overlap simultaneously. -/
lemma net_select (f:I→Site n)(hg: ¬ Edition.Spaced b f) :
    ∃ (J:Type) (_:Fintype J) (_:DecidableEq J) (L:Fibers I J),
      L.twig (L.bunch i)=i ∧ Fintype.card J<Fintype.card I ∧ Edition.Spaced b (f ∘ L.twig) ∧ ∀ x:I,separation (f x) (f (L.twig (L.bunch x)))<b^2:=by
    classical
    let p(a : Finset I):= i∈a∧(a:Set I).Pairwise (fun x y=>b^2≤ separation (f x) (f y)); let S:= univ.filter p; have ht x:x∈S↔ p x:=mem_filter.trans (and_iff_right (mem_univ _))
    have hξ:p {i}:= ⟨mem_singleton_self _,by simp⟩
    obtain ⟨s,hp,hh⟩:= Finset.exists_max_image S Finset.card ⟨{i}, (ht _).2 hξ⟩; have hs: i∈s:=(ht s|>.1 hp).1; have he :=(ht s|>.1 hp).2
    have hX (x:I) (hx:x∉s) : ∃ a∈s,separation (f x) (f a) < b^2:=by
       by_contra! h; have hy:p (insert x s):=by
         refine ⟨mem_insert_of_mem hs,fun i hi j hj hij=>?_⟩; rcases mem_insert.mp hi with hi|ht'; subst i
         · exact h j ((mem_insert.mp hj).resolve_left hij.symm)
         rcases mem_insert.mp hj with rfl|hh'; · rw [separation_comm]; exact h i ht'
         exact he ht' hh' hij
       have hu:=hh (insert x s) ((ht _).2 hy); rw [card_insert_of_notMem hx] at hu; omega
    have h₀:∀ x, ∃ j : (↑s:Type), separation (f x) (f j.val)< b^2 ∧ (x∈s→j.val=x):=by
       intro x; by_cases ht:x∈s
       · exact ⟨⟨x,ht⟩, by simpa only [separation_self] using (pow_pos hb 2), fun _=>rfl⟩
       obtain ⟨j,hj,H⟩:=hX x ht; exact ⟨⟨j,hj⟩,H,fun h=> (ht h).elim⟩
    choose K hK hJ using h₀; let F:Fibers I (↑s:Type):= ⟨K,Subtype.val,fun x=> Subtype.ext (hJ x x.property)⟩
    refine ⟨_,inferInstance,inferInstance,F,hJ i hs,?_ ,fun i j hij=> he i.property j.property (mt Subtype.ext hij),hK⟩
    rw [Fintype.card_coe]; refine lt_of_le_of_ne (Finset.card_le_univ _) ?_; intro H; rw [Finset.eq_univ_of_card s H] at he; exact hg (fun i j hij=> he (mem_univ i) (mem_univ j) hij)

def Collar (o:V×I→Site n)(v:V)(E:V→Site n)(P:V→Motion) := ∀ w,w≠v→∀ b:I,o (w,b) = affine (P w).1 (E w) (o (v,b))
def Cross (b:ℕ)(o:V×I→Site n) := ∀ i j:V×I,i.1≠j.1→ b^2 ≤ separation (o i) (o j)
lemma Collar.shrunk (h: Collar o v E P)(F:Fibers I J) : Collar (o ∘ (partialGroup V F).twig) v E P := fun j hj x=>h j hj _
lemma Cross.shrunk (h: Cross b o)(F:Fibers I J): Cross b (o ∘ (partialGroup V F).twig):= fun i j hij=> h _ _ hij
lemma Collar.widths (h:Collar o v E P)(w:V)(i j:I) : separation (o (w,i)) (o (w,j))=separation (o (v,i)) (o (v,j)):=by
    by_cases he:w=v; · rw [he];
    rw [h w he i,h w he j]; simp [affine,separation_signed,separation_translate]
lemma Cross.together (h:Cross b o)(hT:Collar o v E P)(hs:Edition.Spaced b (fun i:I=>o (v,i))) : Edition.Spaced b o:=by
    rintro ⟨i,b⟩ ⟨j,c⟩ hp; by_cases ht:i=j; · subst j; rw [hT.widths i]; exact hs b c (by rintro rfl; exact hp rfl)
    exact h _ _ ht

-- halo toll upper
include hb in
lemma pairCover (x y : Site n)(a:ℕ)(h:separation x y ≤ a*b) : coverNumber b ({x,y}:Support n) ≤ (2*a+1)^4:=by
    refine (Corona.cover_mono (show ({x,y}:Support _)⊆ halo (a*b) {x} from ?_) b).trans ?_
    · intro i hi; rcases mem_insert.mp hi with hi|hi
      · subst i; exact halo_spec.mpr ⟨x,mem_singleton_self _,by rw [separation_self]; exact Nat.zero_le _⟩
      rw [mem_singleton.mp hi]; exact halo_spec.mpr ⟨x,mem_singleton_self _,h⟩ -- orientation?
    simpa only [two_mul] using Corona.tile x a b hb

variable (X:History G)
-- hidden notations with local lets in headings sometimes tricky
set_option quotPrecheck false
local notation "Y'" => X.levels.budget
local notation "L" => X.S.block
/-- Upward propagated opacity of a first-time near hit, pays for the halo **before**
stepping. -/
def carpet (A:History G)(i:ℕ) : ℕ := 16*OPE.haloUnits (A.S.block i) (A.levels.budget i).B (A.levels.budget (i+1)).B
lemma submerged (m p:ℕ) (x y:Site (X.S.side (m+1) p))
    (h: let S:=X.levels.clock.op m p; separation (S.ratio.parent x) (S.ratio.parent y) < ((Y' m).B)^2) : coverNumber (Y' (m+1)).B {x,y} ≤ carpet X m:=by
    let S:= (X.levels.clock.op m p).ratio; let Z:=(L m).val; have hm:S.count.val=Z:=rfl
    let K:=(Y' m).B; let B:= (Y' (m+1)).B; have hp: Odd S.count.val:=by rw [hm]; exact X.S.block_odd m
    have hZ j:2*separation j (S.embed (S.parent j)) < Z:= midway S hp j
    have hx:=separation_triangle x (S.embed (S.parent x)) y; have hf:= separation_triangle (S.embed (S.parent x)) (S.embed (S.parent y)) y; rw [Station.both,hm,separation_comm (S.embed (S.parent y)) y] at hf -- orientation which?
    have hy':Z*separation (S.parent x) (S.parent y) < Z*K^2:= Nat.mul_lt_mul_of_pos_left h (L m).property
    have hb j: 1 ≤ (Y' j).B:= (Y' j).B_pos
    let c:= Z * (K+B+1)^2; have hk: K^2+1 ≤ (K+B+1)^2:= by rw [show (K+B+1)^2=K^2+1 + (B*B+2*(K*B+B+K)) from (by ring)]; omega
    have hv:=Nat.mul_le_mul_left Z hk; rw [mul_add,mul_one] at hv
    have hS: separation x y ≤ c:=by dsimp only [c]; have he:=hZ x; have he':=hZ y; -- need Z difference quantitative h ≤ K²-1?
                                              omega
    refine (pairCover (b:=B) ?_ x y c ?_).trans ?_
    · exact hb (m+1)
    · exact hS.trans (by have h := Nat.mul_le_mul_left c (hb (m+1)); rw [mul_one] at h; exact h)
    change (2*c+1)^4 ≤ 16*(1+c)^4; calc _ ≤ (2*(1+c))^4:= by gcongr; omega
                                          _ = _:=by ring
lemma selectIf {m p:ℕ}
    (E:V→Site (X.S.side m p))(P:V→Motion)(v:V)(o:V×I→Site (X.S.side m p)) (q:V×I→Site (X.S.side (m+1) p)) (h:Collar o v E P)(hv:Cross (Y' m).B o)
    (ht:(X.levels.clock.op m p).ratio.parent ∘ q=o)(hc:¬ Edition.Spaced (Y' m).B o) :
    ∃ (J:Type)(_ : Fintype J)(_ : DecidableEq J)(F:Fibers I J), F.twig (F.bunch i)=i ∧ Fintype.card J<Fintype.card I∧ Edition.Spaced (Y' m).B (o ∘ (partialGroup V F).twig) ∧ ∀ j:V×I, coverNumber (Y' (m+1)).B ({q (j.1,F.twig (F.bunch j.2)),q j}:Support _) ≤ carpet X m:=by
    let b := (Y' m).B; obtain ⟨J,U,V',F,hH,hK,he,hB⟩:= net_select (b:=b) i (Y' m|>.B_pos) (fun i:I=>o (v,i)) (fun he=>hc (hv.together h he))
    refine ⟨J,U,V',F,hH,hK,(hv.shrunk F).together (h.shrunk F) he,fun j=>?_⟩; apply submerged; dsimp only; rw [(show ∀ j,(X.levels.clock.op m p).ratio.parent (q j)=o j from congr_fun ht) _,(show ∀ j,(X.levels.clock.op m p).ratio.parent (q j)=o j from congr_fun ht) _,separation_comm]
    cases j; rw [h.widths]; exact hB _
end YM.MergeProof.Ribbons.ManyCopies
