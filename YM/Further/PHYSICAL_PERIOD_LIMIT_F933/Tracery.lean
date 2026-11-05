import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Macrame

/-!
# Glazers between two actual Patch steps

Packed around a common patch, explicit all labels including motion. In the canonical
use `large` does not require any harmonic tie across periods. This is strictly
a same-input T comparison, for virtual periods NOT asked in Schedule but full step
still definable and analytic there; no invocation of H/B there. `hwrap` genuine
c>1.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Macrame
open Push.Uniform Precision Function Shingle Lattice Gauge Tree RG Wilson Exterior Filter Finset Set Push
open scoped BigOperators Topology Classical
variable {c C f F : Side} {P : Patch} (Q : KernelChoices)
  {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {M : ℕ}

abbrev stepped (h : f.val=c.val*P.L.val) : StepData c f := ⟨P,Q,h⟩
abbrev decreed (h : f.val=c.val*P.L.val) : Ratio c f := ⟨P.L,h⟩
structure Lace (h : f.val=c.val*P.L.val) (H : F.val=C.val*P.L.val) (M : ℕ) where
  low : Window c C M
  high : Window f F M
  stake x : high.cut ((decreed H).embed x)=(decreed h).embed (low.cut x)
  legal : 2 ≤ c.val
  taller : 2 ≤ C.val
namespace Lace
variable (L : Lace h H M)
abbrev R (_L : Lace h H M) := decreed H
abbrev r (_L : Lace h H M) := decreed h
lemma regions (i : Site C) (x : Site P.L) : L.high.cut (L.R.assemble (i,x)) = L.r.assemble (L.low.cut i,x) := by
  unfold Ratio.assemble; dsimp only; rw [L.high.port,L.stake]
lemma position (i : Site F) : L.r.parent (L.high.cut i)= L.low.cut (L.R.parent i) := by
  obtain ⟨⟨j,x⟩,rfl⟩:= L.R.assemble_bijective.2 i
  rw [L.regions,Ratio.assemble_parent,Ratio.assemble_parent]
lemma room (i : Site F) : L.r.residue (L.high.cut i)= L.R.residue i := by
  obtain ⟨⟨j,x⟩,rfl⟩:= L.R.assemble_bijective.2 i
  rw [L.regions,Ratio.assemble_res,Ratio.assemble_res]

-- no false crossing comparison at c=1
lemma advance (L : Lace h H M) (x : Site F) (i : Axis) :
    L.R.parent (x+step i)=L.R.parent x ↔ L.r.parent (L.high.cut x+step i)=L.r.parent (L.high.cut x) := by
  have hp := P.odd_side
  rw [L.R.parents_hop hp,L.r.parents_hop hp,L.room]
  have hn {n : Side} (h : 2 ≤ n.val) (x : Site n) : x+step i≠x := by
    letI : Fact (1<n.val):=⟨h⟩
    intro he; have hx := congr_fun he i; simp [Per] at hx
  split <;> rename_i h'
  · simp only [hn L.legal _,hn L.taller _]
  simp
lemma strolls (x : Site F) (i : Lattice.Step) :
    L.R.parent (x+i.vec)=L.R.parent x ↔ L.r.parent (L.high.cut x+i.vec)=L.r.parent (L.high.cut x) := by
  rcases i with ⟨i,_|_⟩
  · exact L.advance x i
  have he:= L.advance (x-step i) i
  rw [L.high.step_down,sub_add_cancel,sub_add_cancel] at he
  simpa only [Lattice.Step.vec,↓reduceIte, sub_eq_add_neg] using Iff.trans eq_comm (he.trans eq_comm)
lemma fork (x : Site F) : leaf L.R x ↔ leaf L.r (L.high.cut x) := by
  unfold leaf; change (¬ x=L.R.embed _) ↔ ¬ _
  rw [L.R.root_id,L.r.root_id,L.room]

-- for all uses we choose constant arbitrary tags => same schedule c'. Also works genuine frames (input analytic branches already checked all t).
def pullTag (t : (stepped Q h).Choices) : (stepped Q H).Choices :=
  ⟨fun x=> t.1 (L.low.cut x), fun i=> t.2 (L.low.cut i.1,i.2)⟩

-- choose arbitrary constant over sites in both periods; HEq trivial
def plain : (stepped Q h).Choices := ⟨fun _=> Classical.arbitrary P.FrameTag,fun _=> Classical.arbitrary P.Points⟩

lemma plain_binding : L.pullTag Q (plain Q (h:=h))=plain Q := rfl

variable {G : Gauge}
lemma fountains (t : (stepped Q h).Choices) (U : Config G f) (i : Site C) :
    (stepped Q H).frames (L.high.links U) (L.pullTag Q t).1 i=(stepped Q h).frames U t.1 (L.low.cut i) := by
  unfold StepData.frames pullTag; dsimp only
  rw [L.high.expansion,show (stepped Q H).ratio.embed i=L.R.embed i from rfl,L.stake]; rfl
lemma predicts (t : (stepped Q h).Choices) (U : Config G f) :
    (stepped Q H).prediction (L.high.links U) (L.pullTag Q t)=L.low.links ((stepped Q h).prediction U t) := by
  funext e
  have hf := L.fountains Q t U
  let T := L.pullTag Q t
  change P.predict Q ((stepped Q H).connector (L.high.links U) T.1 e) (t.2 (L.low.cut e.1,e.2))=
    P.predict Q ((stepped Q h).connector U t.1 _) _
  have hu : (stepped Q H).connector (L.high.links U) T.1 e=(stepped Q h).connector U t.1 (L.low.cut e.1,e.2) := by
    funext x
    unfold StepData.connector; dsimp only
    rw [show (stepped Q H).ratio.embed e.1=L.R.embed e.1 from rfl,L.high.expansion,L.stake, show (stepped Q H).frames _ _ e.1=_ from L.fountains Q t U e.1,
      show (stepped Q H).frames _ _ (e.1+step e.2)=_ from L.fountains Q t U (e.1+step e.2),L.low.step_up]; rfl
  rw [hu]
def repeater (A : Forest L.r) : Forest L.R where
  up x := A.up (L.high.cut x)
  height x := A.height (L.high.cut x)
  bound x := A.bound _
  rise x h := by rw [L.high.uniform]; exact A.rise _ ((L.fork _).mp h)
  stays x h := (L.strolls _ _).mpr (A.stays _ ((L.fork _).mp h))

-- Compatible forest pair can also be used with translations.
structure Fitted (A : Forest L.r) (B : Forest L.R) : Prop where
  rise x : B.up x=A.up (L.high.cut x)

variable {L} {A : Forest L.r} {B : Forest L.R} (hp : L.Fitted A B)
namespace Fitted

include hp
lemma pines (i : Edge (Site F)) : i∈ B.trunks ↔ (L.high.cut i.1,i.2) ∈ A.trunks := by
  rw [Tree.Forest.trunk_mem_iff,Tree.Forest.trunk_mem_iff]; constructor
  · rintro ⟨x,hk,H⟩; refine ⟨_, (L.fork _).mp hk, ?_⟩
    rw [← hp.rise, ← L.high.used,H]; rfl
  rintro ⟨y,H,hq⟩
  cases hv : A.up y with
  | mk k b =>
    cases b
    · rw [hv] at hq
      change (y,k)=(L.high.cut i.1,i.2) at hq
      have hh := Prod.mk.inj hq
      refine ⟨i.1,(L.fork _).mpr (hh.1 ▸ H),?_⟩
      rw [hp.rise, ← hh.1,hv]; exact Prod.ext rfl hh.2
    rw [hv] at hq
    change (y-step k,k)=(L.high.cut i.1,i.2) at hq
    have HH := Prod.mk.inj hq; have h : L.high.cut i.1+step k=y := by rw [← HH.1]; abel
    refine ⟨i.1+step k,(L.fork _).mpr ?_,?_⟩
    · rw [L.high.step_up,h]; exact H
    rw [hp.rise, L.high.step_up,h,hv]; change (i.1 + step k-step k,k) = i; rw [add_sub_cancel_right,HH.2]

-- Addresses across Cover and Per
omit hp in
def narrow (L : Lace h H M) : Primary C G → Primary c G := fun i=> ((L.low.cut i.1.1,i.1.2),i.2)
def limb (i : B.Free) : A.Free := ⟨(L.high.cut i.val.1,i.val.2),fun ht=>i.property ((hp.pines i.val).2 ht)⟩
def track (hp : L.Fitted A B) : Key B G → Key A G := fun i => (hp.limb i.1,i.2)
def bores (hp : L.Fitted A B) := Sum.map (narrow L (G:=G)) (hp.track (G:=G))

omit hp in
lemma replicate (L : Lace h H M) (V : Config G c) : replica L.R (L.low.links V)=L.high.links (replica L.r V) := by
  funext i; unfold replica Window.links; dsimp only
  split <;> rename_i hi
  · rw [if_pos ((L.advance i.1 i.2).mp hi)]
  rw [if_neg (mt (L.advance i.1 i.2).mpr hi), L.position]


lemma governs (x : Positions (Joint A G)) :
    fine G B (x ∘ hp.bores)=L.high.links (fine G A x) := by
  have hV : outer G B (x ∘ hp.bores)=L.low.links (outer G A x) := by funext i; rfl
  let W := outer G A x; let Y := (paint A G x).2
  funext i
  change B.drape _ i = A.drape _ (L.high.cut i.1,i.2)
  by_cases Hh:i∈B.trunks
  · exact (B.on_tree _ ⟨i,Hh⟩).trans ((A.on_tree _ ⟨_,(hp.pines _).mp Hh⟩).symm)
  let k : B.Free := ⟨i,Hh⟩
  let K := hp.limb k
  let j := K.val
  change B.drape (fun r=>G.lieExp _ * replica L.R (outer G B _) r.val) k.val = A.drape (fun r=>G.lieExp (Y r) * replica L.r W r.val) K.val
  rw [B.off_tree _ k,A.off_tree _ K]
  rw [hV,Fitted.replicate L]; rfl
lemma appraisal (x : Positions (Joint A G)) (t : (stepped Q h).Choices) (p : Clip) (R : PathData G) :
    Uniform.priced B (L.pullTag Q t) p R (x ∘ hp.bores)= (M:ℝ)*Uniform.priced A t p R x := by
  unfold Uniform.priced tested; let U := outer G A x; let V := fine G A x
  change mainTerm p R (fine G B (x ∘ hp.bores))+ noiseTaylor (stepped Q H) (outer G B _) (fine G B _) (L.pullTag Q t)=(M:ℝ)*(mainTerm p R V+noiseTaylor (stepped Q h) U V t)
  have hx := L.high.revenue p R V
  rw [mul_add]; refine congr_arg₂ (fun a b:ℝ=>a+b) ((congr_arg (mainTerm p R) (hp.governs x)).trans hx) ?_
  suffices he : noiseTaylor (stepped Q H) (L.low.links U) (L.high.links V) (L.pullTag Q t) = (M:ℝ)*noiseTaylor (stepped Q h) U V t by
    exact ((congr_arg (fun v : Config G F=>noiseTaylor (stepped Q H) (L.low.links U) v (L.pullTag Q t)) (hp.governs x)).trans he)
  unfold noiseTaylor; rw [L.predicts]
  let Y := (stepped Q h).prediction V t
  change Q.penalty*(∑ e:Edge (Site C),G.price (L.low.links U e * (L.low.links Y e)⁻¹)) = (M:ℝ)*(Q.penalty*∑ e:Edge (Site c),G.price (U e * (Y e)⁻¹))
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; unfold Window.links; dsimp only
  have he := multiplied L.low.cut L.low.fold (fun y:Site c=> ∑i:Axis,G.price (U (y,i)*(Y (y,i))⁻¹))
  rw [he,nsmul_eq_mul]; ring
end Fitted
end Lace
end YM.Further.PhysicalPeriodLimitF933.Macrame
