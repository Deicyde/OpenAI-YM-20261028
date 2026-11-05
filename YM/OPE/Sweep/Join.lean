import YM.OPE.Sweep.Step

/-!
# Partially group, purchase and radii
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {Z V I J T : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side}
variable {A:History G}{N p k i j:ℕ}
    {δ φ σ χ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
    {E:∀ i:ℕ, V→Site (A.S.side i p)}{P:V→Motion}{v:V}{B:V→Equiv.Perm V}{o:∀ i:ℕ,V×I→Site (A.S.side i p)}
set_option quotPrecheck false
local notation "R" => A.rep N p
local notation "Y'" => A.levels.budget
variable {Q:∀ i:ℕ,i≤N→ Config G (A.S.side i p)→Poly (Names V I)} {W W':I→ℝ}{c: V×I→ℂ}
local notation "e" => (Y' i).supportExponent

/-- Generic toll for a slot involved in a group surgery away from the final
horizon. -/
def license (A:History G)(δ : ℕ→ℝ)(H l i : ℕ):= (δ i/H)*δ i / Real.exp (((A.levels.budget i).supportExponent+1/2)*l)
def grouped (A:History G)(δ:ℕ→ℝ)(H l i:ℕ)(W:I→ℝ)(L:Fibers I J)(a:J):=
    ∏ x∈L.contents a, license A δ H l i*W x
def cashIn (A:History G)(δ:ℕ→ℝ)(H l i:ℕ)(W:I→ℝ) := ∏ x,license A δ H l i*W x

variable (H l : ℕ) (L:Fibers I J)
lemma license_pos (hF:0<δ i)(hH:0<H): 0< license A δ H l i:=by unfold license; positivity
lemma grouped_pos (hF:0<δ i)(hH:0<H)(hW:∀ x,0<W x)(a:J): 0<grouped A δ H l i W L a:= Finset.prod_pos (fun j _=> mul_pos (license_pos H l hF hH) (hW _))
lemma cashIn_pos (hF:0<δ i)(hH:0<H)(hW:∀ x,0<W x):0< cashIn A δ H l i W:= Finset.prod_pos (fun j _=> mul_pos (license_pos H l hF hH) (hW _))
lemma grouped_b (a:V×J): grouped A δ H l i W L a.2 = ∏ j∈(partialGroup V L).contents a, Fibers.Salt.tow (fun z:V×I=> δ i*W z.2) (e+1/2) (δ i/H) l j:=by
    unfold grouped license; rcases a with ⟨v,a⟩; rw [contentP,prod_image]; refine prod_congr rfl fun i _=>?_ ; unfold Fibers.Salt.tow; dsimp only; ring
    exact fun _ _ _ _ h=> Prod.mk_inj.mp h |>.2
lemma cashIn_b (j₀:I)(a:V) : cashIn A δ H l i W = ∏ j∈(finishGroup V j₀).contents a, Fibers.Salt.tow (fun z:V×I=>δ i*W z.2) (e+1/2) (δ i/H) l j:=by
    unfold cashIn license; rw [contentF,prod_image]; refine prod_congr rfl fun i _=>?_ ; unfold Fibers.Salt.tow; dsimp only; ring
    exact fun _ _ _ _ h=> Prod.mk_inj.mp h |>.2
lemma groupCash (i:ℕ)(A:History G)(W:I→ℝ): (∏ j,grouped A δ H l i W L j)=cashIn A δ H l i W:=by
    symm; unfold cashIn; let p:(Bud J).Mode:=⟨univ,mem_univ _⟩
    rw [show ((univ:Finset I))=(L.plena p).val from Finset.ext fun x=> (Fibers.reaped L p x|>.trans ⟨fun _=>mem_univ _,fun _=>mem_univ _⟩)|>.symm]
    exact L.prod_plena p _
lemma cashIn_a : cashIn A δ H l i W=(license A δ H l i)^(Fintype.card I)*∏ x,W x := by simp only [cashIn,prod_mul_distrib,prod_const,card_univ]

lemma cardinal_le (hF:Fintype.card I≤H) : ∀ a:V×J,((partialGroup V L).contents a).card ≤ H := by
    rintro ⟨v,a⟩; rw [contentP]; exact Finset.card_image_le.trans ( (Finset.card_le_univ _).trans hF)
lemma cardinal_leF (i₀:I)(hF:Fintype.card I≤H) : ∀ a:V,((finishGroup V i₀).contents a).card ≤ H:=by
    intro a; rw [contentF]; exact Finset.card_image_le.trans hF

local notation "Y*" => ((Y' i).B)
local notation "a" => scurry A.levels r χ (δ i) i
structure ClusterPars (A:History G) (δ χ:ℕ→ℝ) (r:ℕ→ℕ) (i:ℕ) : Prop where
    crisp : χ i≤1
    funs : 0<δ i∧ δ i ≤ 1
    bars : (((A.levels.budget i).B+(A.levels.budget i).B+1:ℕ):ℝ)^4*scurry A.levels r χ (δ i) i ≤ 1/2 ∧ Real.exp (scurry A.levels r χ (δ i) i)-1≤1
local notation "Γ" => (Y' i).B
variable (h:A.Selected) (hn:i≤N) (hc:Live A N p E o P v B Q δ χ i hn W c)
    (hr:ClusterPars A δ χ r i)
    (hf:Arsenal (A.rep N p i)) (hH:0<H)(hF:Fintype.card I ≤ H) (hO:Occupancy (o i) (r i))
    (hp:∀ j,j≠v→∀ b:I,o i (j,b)=affine (P j).1 (E i j) (o i (v,b)))
local notation "Q'"=> (fun x hx U=> Fibers.reap (partialGroup V L) (Q x hx U))
local notation "o'"=> (fun x=>o x ∘ (partialGroup V L).twig)
include h hn hc hr hf hH hF hO hp
lemma Live.gathers (hS:∀ j:V×I, coverNumber Γ ({o i (j.1,L.twig (L.bunch j.2)),o i j}:Support _) ≤ l) : Under A N p E o' P v B Q' i hn (fun x=>grouped A δ H l i W L x/8) 0:=by
    obtain ⟨g,K,hh⟩:= hc.now; have hA:= h.represents N p i hn; let w(j:V×I):=δ i*W j.snd; have hx(j):0<w j:= mul_pos hr.funs.1 (hc.width _)
    let b(j:V×J):=grouped A δ H l i W L j.2; let Ξ:=partialGroup V L
    obtain ⟨g',K',he,hB,hT⟩:= partialFuse (C':=b) (Z:=1) H (r i) l hf (hA.vac.symm ▸ hh) hA.good.labels (fun j hj k=>⟨hp j hj k,hc.toUnder.carries _ hj k⟩) hx hO zero_le_one (fun j=> (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hc.width j.2|>.le) hr.funs.2) (norm_nonneg _)).trans (hc.affordable j)) hr.funs.1 hr.funs.2 (by norm_num) (by norm_num) hH (fun U=>(Tour.bright A h N p i hn U).ne') (by rw [hA.vac]; exact hr.bars.1) (by rw [hA.vac]; exact hr.bars.2) (cardinal_le H L hF) (fun j=> by rw [hA.vac]; exact hS j) (fun j=>by rw [hA.vac]; exact grouped_b H l L j)
    have hu(x): 0 < grouped A δ H l i W L x:= grouped_pos H l L hr.funs.1 hH hc.width x; have hv(x:V×J): 0<b x/8:= div_pos (hu _) (by norm_num)
    refine ⟨fun x=> hv (v,x),fun j=>?_,g',K',fun x=>?_ ,fun j=>(hB j).1,hT,?_⟩
    · simp
    · apply (hB (v,x)).2.more; apply le_of_eq; change 4*((1:ℝ)/b (v,x))=1/(2*(b (v,x)/8)); ring
    rw [← hA.vac]; exact he.prune (fun j=> hu j.2) hv (slighter (fun j=>hu j.2) hv (w:=1) (fun j=> ((div_le_self (hu j.2|>.le) (by norm_num : (1:ℝ)≤8))).trans_eq (one_mul _|>.symm)) zero_le_one le_rfl) zero_le_one (by simp) (by norm_num)
lemma Live.terminal (i₀:I)(hS:∀ j:V×I, coverNumber Γ ({o i (j.1,i₀),o i j}:Support _) ≤ l) :
    let t:=cashIn A δ H l i W
    ∃ g:V → Config G (A.S.side i p)→ℂ, ∃ T: V→ℕ → Config G (A.S.side i p)→ℂ,
       Served (R i) g (fun j=>profile (R i).activities (T j)) (fun U=>Fibers.reap (finishGroup V i₀) (Q i hn U)) (fun j=>o i (j,i₀)) (fun _=>t) e 1 ∧
       (∀ j,Dominated (T j) ∧ Blade (R i) (o i (j,i₀)) (g j) (profile (R i).activities (T j)) 0 (4*(1/t))) ∧
       (∀ j,j≠v→ g j=stepUp (P j) (E i j) (g v) ∧ profile (R i).activities (T j)=floatUp (P j) (E i j) (profile (R i).activities (T v))) := by
    obtain ⟨g,K,hh⟩:= hc.now; have hA:= h.represents N p i hn; let w(j:V×I):=δ i*W j.snd; have hx(j):0<w j:= mul_pos hr.funs.1 (hc.width _)
    intro t
    obtain ⟨g',K',he,hB,hT⟩:= terminalFuse (C':=fun _=>t) (Z:=1) H (r i) l hf (hA.vac.symm ▸ hh) hA.good.labels (fun j hj k=>⟨hp j hj k,hc.toUnder.carries _ hj k⟩) hx hO zero_le_one (fun j=> (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hc.width j.2|>.le) hr.funs.2) (norm_nonneg _)).trans (hc.affordable j)) hr.funs.1 hr.funs.2 (by norm_num) (by norm_num) hH (fun U=>(Tour.bright A h N p i hn U).ne') (by rw [hA.vac]; exact hr.bars.1) (by rw [hA.vac]; exact hr.bars.2) (cardinal_leF H i₀ hF) (fun j=> by rw [hA.vac]; exact hS j) (fun j=>by rw [hA.vac]; exact cashIn_b H l i₀ j)
    exact ⟨g',K',hA.vac ▸ (show Served (R i) g' (fun j=>profile (R i).activities (K' j)) _ (fun j=>o i (j,i₀)) _ (R i).p.supportExponent 1 from he),hB,hT⟩
end YM.MergeProof.Ribbons.ManyCopies
