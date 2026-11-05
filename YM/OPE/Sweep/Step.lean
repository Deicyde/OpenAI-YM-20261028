import YM.OPE.Grouping.Replicate
import YM.OPE.Replicas.Muscat
import YM.OPE.Replicas.ManyBudgets
/-!
# Simultaneous rough group estimate, one step

Based on the `musky` propagation lemma. This invariant at one level
allows partially grouped families and prices that spend only on a step
that groups at least two insertions.
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

private lemma tow_reprices {P:T→Z→Poly (Names V I)} {F:T→Support n}{W W':V×I→ℝ}
    {b:ℕ}{v u:ℝ}(h:Towed W F P b u v)(hw: W'≤ W)(hy:∀ i,0≤ W' i): Towed W' F P b u v:=by
    obtain ⟨a,hx,he,hA⟩:=h; refine ⟨a,hx,he,fun i=>?_⟩; obtain ⟨s,hx,ht,he⟩:=hA i
    exact ⟨s,hx,ht, (Finset.sum_le_sum (f:=fun i=> Poly.toll W' i*s i) fun i _=> mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun i _=>hy i) (fun i _=>hw i)) (hx i)).trans he⟩

lemma Arc.reprice {R:Rep G n}{g K Q v a m B o χ η δ x d c}{W W':V×I→ℝ} (h:Arc R g K Q v a m B o W χ η δ x d c) (hw: W'≤W)(hy:∀ i, 0≤ W' i) : Arc R g K Q v a m B o W' χ η δ x d c:=by
    obtain ⟨F,T,ψ,hξ,hZ,hT,hV,H⟩:= h.see
    refine ⟨F,T,ψ,⟨hξ.yes,hξ.tracks,?_⟩,hZ,tow_reprices hT hw hy,tow_reprices hV hw hy,H⟩; intro i; obtain ⟨u,hu,ht⟩:=hξ.fee i; exact ⟨u,hu, le_trans (Finset.sum_le_sum (fun j _=> mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hw i) (hu j).1) (Real.exp_pos _).le)) ht⟩

variable {A:History G}{N p k i:ℕ}
    {δ φ σ χ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
    {E:∀ i:ℕ, V→Site (A.S.side i p)}{P:V→Motion}{v:V}{B:V→Equiv.Perm V}{o:∀ i:ℕ,V×I→Site (A.S.side i p)}
set_option quotPrecheck false
local notation "Γ" => A.levels.clock.op i p
local notation "R" => A.rep N p
local notation "Y'" => A.levels.budget
variable {Q:∀ i:ℕ,i≤N→ Config G (A.S.side i p)→Poly (Names V I)} {W W':I→ℝ}{c: V×I→ℂ}
-- Full price at a single level. δ furnished just for grouping.
-- o,E defined globally for composition.
structure Under (A:History G)(N p:ℕ) (E:∀ i:ℕ, V→Site (A.S.side i p))(o:∀ i:ℕ,V×I→Site (A.S.side i p))(P:V→Motion)(v:V)(B:V→Equiv.Perm V)
    (Q:∀ i:ℕ,i≤N→ Config G (A.S.side i p)→Poly (Names V I)) (i:ℕ)(hn:i≤N)(W:I→ℝ)(c:V×I→ℂ) : Prop where
    width j: 0< W j
    affordable j: W j.2*‖c j‖≤1
    flor : ∃ g:(V×I)→ Config G (A.S.side i p)→ℂ,∃ K:(V×I)→ℕ→ Config G (A.S.side i p)→ℂ,
       (∀ b:I,Blade (A.rep N p i) (o i (v,b)) (g (v,b)) (profile (A.rep N p i).activities (K (v,b))) (c (v,b)) (1/(2*W b))) ∧ (∀ j,Dominated (K j)) ∧ May v P (E i) B g (fun j=> profile (A.rep N p i).activities (K j)) c ∧ Serves (A.rep N p i) g (fun j=> profile (A.rep N p i).activities (K j)) (Q i hn) v P (E i) B (o i) (W ∘ Prod.snd) ((A.levels.budget i).supportExponent) 1
structure Live (A:History G)(N p:ℕ) (E:∀ i:ℕ, V→Site (A.S.side i p))(o:∀ i:ℕ,V×I→Site (A.S.side i p))(P:V→Motion)(v:V)(B:V→Equiv.Perm V)
    (Q:∀ i:ℕ,i≤N→ Config G (A.S.side i p)→Poly (Names V I)) (δ χ:ℕ→ℝ) (i:ℕ)(hn:i≤N)(W:I→ℝ)(c:V×I→ℂ) : Prop extends Under A N p E o P v B Q i hn W c where
    now : ∃ g K, Arc (A.rep N p i) g K (Q i hn) v P (E i) B (o i) (fun j=>δ i*W j.2) ((A.levels.budget i).supportExponent+1/2) ((A.levels.budget i).supportExponent+1) 1 (χ i) (δ i) c

lemma Under.carries {hi:i≤N} (h:Under A N p E o P v B Q i hi W c) (v':V)(hv:v'≠v)(j:I) : c (v',j)=scalar (P v') (c (v,j)):= by obtain ⟨g,K,-,-,hf,-⟩:=h.flor; exact ((hf _ hv).2 j).2.2

variable (h:A.Selected)(ht:Thor A δ r D σ χ k)
include h ht
local notation "L" => ((A.S.block i).val:ℝ)
local notation "e" => (Y' i).supportExponent
local notation "x" => (6*L:ℝ)
lemma Under.evens (hi:k ≤ i)(hn:i<N) (hc:Under A N p E o P v B Q (i+1) hn W c)
    (hf: E (i+1)=fun j=>(Γ).ratio.embed (E i j))
    (hb:∀ j,j≠v→∀ b:I,o (i+1) (j,b)=affine (P j).1 (E (i+1) j) (o (i+1) (v,b)))
    (hΔ: Q i hn.le=(Γ).push (R (i+1)).beta (Q (i+1) hn))
    (hp:Integrable (Q (i+1) hn) (prior G _))
    (hx: (Γ).ratio.parent ∘ o (i+1)=o i) (hV: Occupancy (o (i+1)) (r i)) (hg:Occupancy (o i) (r i))
    (hY: MergeProof.Float.Runs (D N p i hn) Γ x)
    (he:x ≥ 1)
    (hJ:Drake (Names V I) (Y' i).B (o i)) (hF:Brine A k δ φ)(hy:φ i≤1) (hw:∀ j,x * W' j ≤ W j) (hW:∀ j,0<W' j): Live A N p E o P v B Q δ χ i hn.le W' c:=by
    have ha(j:I):W' j ≤ W j:= (le_mul_of_one_le_left (hW j|>.le) he).trans (hw j)
    obtain ⟨g,K,hb',hd,he',hR⟩:=hc.flor; have hA:= ht.suns i hi; obtain ⟨hK,hh⟩:=ht.moon N p i hi hn
    let d(b:I):=(1:ℝ)/(2*W b); have hv(j:V×I):2*(W ∘ Prod.snd) j*d j.snd ≤1:= by change 2*W j.2*(1/(2*W j.2))≤1; rw [mul_div_cancel₀ _ (by have he:= hc.width j.2; positivity)];
    obtain ⟨g',F,hG,hF',hφ,hC,hU⟩:= flaring A r h hn hA hK hh (fun (j:V×I)=>hc.width j.2) (hf ▸ hR) (by linarith only) hV (hx.symm ▸ hg) (fun _ _ _=>rfl) (fun j hj b=> by rw [show _=E (i+1) j from (congr_fun hf j).symm]; exact hb j hj b) (hf ▸ he') hd hb' hv hY (zero_le_one.trans he) hp
    have hPeg : Repegs (o i) (Y' i).B (fun j=>δ i*(W ∘ Prod.snd) j) (W' ∘ Prod.snd) (1/2) 1 (Names V I):=by
       apply hJ.palms (fun j=>?_ ) (fun j=>hW j.2) (fun j=> mul_pos hA.hats.1 (hc.width j.2)) (hF.support _ hi); have hz := (hc.width j.2).le
       let u:= mintK (Y' i).B; have ht': 1 ≤ δ i*u := (hF.mint i hi).trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hA.hats.1.le hy) (show 0≤u from (Real.exp_pos _).le))
       refine (ha j.snd).trans ((le_mul_of_one_le_right hz ht').trans_eq ?_); unfold u; ring
    have hT:=descended A N i p r h hn hA (fun j=>hc.width j.2) (fun j=>hW j.2) (hx.symm ▸ hg) (hx.symm ▸ hPeg) hU hG hF'
    rw [hx,← hΔ] at hU hT
    have hA' j: W' j.2*‖c j‖≤1:= (mul_le_mul_of_nonneg_right (ha _) (norm_nonneg _)).trans (hc.affordable j)
    refine ⟨⟨hW,hA',g',F,fun j=>?_ ,hG,hφ,hT⟩,g',F,hU.reprice (fun j=>mul_le_mul_of_nonneg_left (ha _) hA.hats.1.le) (fun j=> mul_nonneg hA.hats.1.le (hW _|>.le))⟩
    have hv:=hC j; rw [hx] at hv; apply hv.more; change x*(1/(2*W j)) ≤ 1/(2*W' j); rw [← mul_div_assoc]; have hP:=hc.width j; have ht:=hW j; exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith only [hw j])

lemma Under.solved (hi:k ≤ i)(hn:i≤N) {g K} (hw':∀ j,0<W' j)
    (he:χ i≤1)(hA:Arsenal (R i)) (hB:Arc (R i) g K (Q i hn) v P (E i) B (o i) (W ∘ Prod.snd) (e+1/2) (e+1) 1 (χ i) (δ i) c)
    (hr:∀ j,W j.2*‖c j‖≤1)(hF:∀ v',v'≠v→∀ j:I,c (v',j)=scalar (P v') (c (v,j)))
    (hz:∀ j:I,8*W' j ≤ W j) : Live A N p E o P v B Q δ χ i hn W' c:=by
    have hP:= h.represents N p i hn; have ha:=ht.suns i hi
    have hY(j:I): W' j ≤ W j:= by linarith only [hw' j,hz j]
    have hw(j:I):0<W j:=(hw' _).trans_le (hY _)
    refine ⟨⟨hw',fun j=> (mul_le_mul_of_nonneg_right (hY j.2) (norm_nonneg _)).trans (hr j),?_⟩, ⟨g,K,hB.reprice (fun j=> (mul_le_of_le_one_left (hw' _|>.le) ha.hats.2).trans (hY j.snd)) (fun j=> mul_nonneg ha.hats.1.le (hw' j.2|>.le))⟩⟩
    rw [← hP.vac] at hB
    obtain ⟨g,L',hg,hb,hT⟩:=stem hA hB hP.good.labels hF (fun j=> hw j.2) he (by norm_num) zero_le_one (fun U=>(Tour.bright A h N p i hn U).ne'); refine ⟨g,L',fun j=>?_ ,fun j=>(hg j).1,hb,?_⟩
    · apply (hg (v,j)).2.more; change 2*(1/W j)+2*(χ i/W j) ≤ 1/(2*W' j)
      calc _ ≤ 2*(1/W j)+2*(1/W j):= add_le_add le_rfl (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he (hw j|>.le)) zero_le_two)
           _ = 4/W j:=by ring
           _ ≤ _:= (div_le_div_iff₀ (hw j) (mul_pos (by norm_num) (hw' j))).mpr (by linarith only [hz j])
    rw [← hP.vac]; exact hT.prune (fun j=> hw j.2) (fun j=>hw' j.2) (slighter (fun i=>hw i.2) (fun i=>hw' i.2) (w:=1) (fun i=> (hY i.snd).trans_eq (one_mul _|>.symm)) zero_le_one le_rfl) zero_le_one (by simp) (by norm_num)
end YM.MergeProof.Ribbons.ManyCopies
