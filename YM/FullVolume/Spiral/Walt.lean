import YM.FullVolume.Spiral.Thorn
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Tower
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s c u:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
local notation "A_"=> P.orient
set_option maxHeartbeats 350000
open Forum
open Extra.Histories.InputColumn
open UniformSpace
abbrev Hein (f:Coefficient F n)(Y:Hol G)(P:Desk G n):= f.Format 0 Y P.orient ∧ ∃ u,f.remBound 0 P.orient P.k u
lemma breakH (f g:Coefficient F n)(hx:f.support=g.support)(h:Hein f Y P)(ht:Hein g Y P): Hein (breakP f g) Y P:=by
   let c:=(-1:ℂ); let p:=Extra.Histories.stretch c g; obtain ⟨hf,v,hv⟩:=h; obtain ⟨hg,t,hT⟩:=ht; have hp:p.Format 0 Y (A_):=stretch_format _ hg
   have hS:ForceFormat P.orient.p P.orient.activities 0 (f.forced+p.forced):= ForceFormat.add ⟨hf.forcing,hf.carried,hf.invariant,hf.supported,hf.borel⟩ ⟨hp.forcing,hp.carried,hp.invariant,hp.supported,hp.borel⟩
   let y:=breakP f g; have hz:y.forced=f.forced+p.forced:=by unfold y p breakP Extra.Histories.stretch; dsimp only; simp only [c,neg_smul,one_smul]; abel
   have he k: Reads Y 0 (f.support k) (0:Label G i) (y.regular k):= by
      have he : Reads Y 0 (f.support k) (0:Label G i) (g.regular k):= (congr_fun hx k).symm ▸ ((reads_null_iff ..).mpr ⟨hg.identity_null k,hg.projects k⟩)
      have h:= reads_sub ((reads_null_iff ..).mpr ⟨hf.identity_null k,hf.projects k⟩) he; rw [sub_zero] at h; exact h
   change Hein y _ _; rw [← hz] at hS
   constructor
   · refine ⟨fun i=>?_ ,hf.origin, fun i=> ((reads_null_iff ..).mp (he i)).1,fun i=> ((reads_null_iff ..).mp (he i)).2,hS.forcing,hS.carried,hS.invariant,hS.supported,hS.borel⟩
     exact regular_sub (hf.smooth _) ((congr_fun hx i).symm ▸ (hg.smooth i))
   have h:= stretch_rem c hT; change p.remBound .. at h
   obtain ⟨a,b,H,h'⟩:= rem_tabs.mp hv; obtain ⟨u',q,H',hu⟩:= rem_tabs.mp h; let V:=(a+u')+(b+q)
   refine ⟨V,a+u',b+q,add_nonneg H.first H'.first,add_nonneg H.second H'.second,le_rfl,P.sane,?_,?_⟩
   · obtain ⟨z,hz,hF⟩:= H.regular; obtain ⟨e,he,hG⟩:= H'.regular
     have hk:y.support=p.support:=hx
     rw [hk]; let U:=Local.sumBudget_add hz he; refine ⟨z+e, ?_,fun i=>?_⟩
     · have hb:f.support=p.support:=hx; have V₀:SumBudget (fun i=> P.orient.p.mass (f.support i) (z i)) a:=hz; rw [hb] at V₀; simp_rw [Pi.add_apply,BudgetPoint.mass,mul_add]; exact Local.sumBudget_add V₀ he
     have hh : y.regular i=f.regular i+p.regular i:= by unfold y p breakP Extra.Histories.stretch; dsimp; simp [c,sub_eq_add_neg]
     rw [hh]; exact bound_add ((congr_fun hx i) ▸hf.smooth i) (hp.smooth _) ((congr_fun hx i) ▸hF i) (hG i)
   rw [hz,mul_add];exact ForceCost.add H.forced H'.forced
-- From real Rune & micro budgets. production true.Fake? Invoke elastic only at true path slices.Budgets P.Q Interface.H.; any one.Folder.
variable {R:Rep G n}{S:Rep G m}{Z:Plate F m n}{Q:Desk G m}
local notation "I"=> Extra.Histories.InputColumn.Listing
-- due import.Many Price.Quill
variable (hf:Along Q.orient S)(he:Along P.orient R)
variable (h: Elastic Z Y R S) (K:Keeper Q.orient.p Q.orient.activities)
include hf he h
lemma dotZ (j:F.Index)(f f':Coin F Y Q)(i:I)(hS:(Matric.tell (dots Z K j (f-f') i)).Format 0 Y P.orient): let u:=dots Z K j f i - dots Z K j f' i
   Swerve (Matric.tell u) (Matric.tell (dots Z K j (f-f') i)) Y P:=by
   intro u; let v(g:Coin F Y Q):= book (Size.axis F j) (Coin.uses g); have heq : Well Q.orient Q Q.k:= ⟨⟨rfl,rfl⟩,rfl⟩
   have hv(f:Coin F Y Q):=granted heq Y (Size.axis F j) f
   let X(f:Coin F Y Q):= rack K (v f); have hx(f:Coin F Y Q): (X f).Format 0 Y S:= along_format _ hf (rack_format _ _ (hv f).1)
   let k:=X f; let g:= X f'; have hu (f:Coin F Y Q):(X f).remBound 0 S Q.k ‖f‖:= along_bound _ hf (keeps K _ ((hv f).2)); obtain ⟨v₀,b,hb,hL⟩:= rem_tabs.mp (hu f); obtain ⟨c,d,hc,h₁⟩:= rem_tabs.mp (hu f'); have hA:= hx f; have hB:=hx f'
   rcases i with _|i|i
   · rw [show u=0 from sub_zero (0:Pin F n)]; exact Swerve.piece _ _ hS hS ⟨rfl,rfl,fun _ _ _=> EventuallyEq.rfl⟩
   · change Swerve (Matric.tell (Z.tint i (k.regular i)- Z.tint i (g.regular i))) (Matric.tell (Z.tint i ((Coin.uses (f-f')).1 i))) Y P
     obtain ⟨x,H,hz⟩:=hb.regular; obtain ⟨y,L,hm⟩:=hc.regular; obtain ⟨he',ha⟩:=h.reg i (k.regular i) (g.regular i) (x i) (y i) ⟨hA.smooth i,hA.origin i,hA.identity_null i,hA.projects _⟩ ⟨hB.smooth i,hB.origin i,hB.identity_null i,hB.projects _⟩ (hz i) (hm i)
     refine Swerve.piece _ _ (along_format _ he.sym he') hS ?_; rw [map_sub]; exact he.price.symm ▸ ha
   change Swerve _ (Matric.tell (Z.ink i (stowK K (v (f-f')) i))) _ _
   obtain ⟨x,H,hz⟩:=hb.forced; obtain ⟨y,L,hm⟩:=hc.forced
   obtain ⟨he',ha⟩:=h.force i (k.forced i) (g.forced i) (x i) (y i) ⟨hA.invariant _,hA.borel _,hA.supported _,hA.carried _,hA.forcing _⟩ ⟨hB.invariant _,hB.borel _,hB.supported _,hB.carried _,hB.forcing _⟩ (hz i|>.2) (hm i|>.2)
   refine Swerve.piece _ _ (along_format _ he.sym he') hS ?_; rw [show stowK K (v (f-f')) i=(k.forced i-g.forced i) from ?_]; exact he.price.symm ▸ ha
   change _= (stowK K (v f)-stowK K (v f')) i; rw [← cogent _ _ _ (hv f).2 (hv f').2]; unfold v; rw [map_sub]; rfl -- abbrev
variable (hX:∀ j:F.Index,∀ f:Coin F Y Q,∃ a b:I→ℝ, Summable a∧ Summable b∧∀ i, let u:=Matric.tell (dots Z K j f i); Hein u Y P∧ u.remBound 0 P.orient P.k (a i)∧ F.coeffSize u.x ≤ b i)
omit he h hf
include hX
local notation "u!"=> dots Z K
lemma boom (j:F.Index)(f:Coin F Y Q): let x i:= Matric.tell (u! j f i); Summable (fun i=> (x i).x) ∧ ∀ k V,Summable (fun i=> (x i).forced k V):=by
   obtain ⟨a,b,ha,hb,he⟩:= hX j f; intro x'; refine ⟨?_,fun k V=> (merge_budget (code _) x' P.sane (fun i=>(he i).2.1) ha|>.2.2|>.summable V).prod_symm.prod_factor k⟩
   apply Summable.of_norm; apply Size.series F; exact Summable.of_nonneg_of_le (fun i=>Work.G08.size_nonneg F _) (fun i=>(he i).2.2) hb
-- prism.Statement.Two paths Pencil & Orb Capture. No price.L
include hf he h
variable (R':SectionData F)(V:∀ z:Motion,P.orient.activities.Moves z.1 0)(hs:R'.Sound Y)(hn: 2≤n.val)
lemma points (j:F.Index)(f f':Coin F Y Q): Swerve (breakP (palmF Z K j f) (palmF Z K j f')) (palmF Z K j (f-f')) Y P:=by
   let x i:=Matric.tell (dots Z K j f i); let y i:=Matric.tell (dots Z K j f' i); let o:=code I; let z:=f-f'; let X i:=Matric.tell (dots Z K j z i)
   obtain ⟨t,hv⟩:=boom K hX j f; obtain ⟨u,hq⟩:=boom K hX j f'; obtain ⟨c,hP⟩:=boom K hX j z
   change Swerve (breakP (Extra.Histories.merge o x) (Extra.Histories.merge o y)) (Extra.Histories.merge o X) Y P; rw [← Matric.melt o t u hv hq]; let W i:= breakP (x i) (y i)
   obtain ⟨a,b,hA,hB,hG⟩:= hX j z
   exact Swerve.mortar o (fun i=> dotZ hf he h K j f f' i (hG i|>.1.1)) (t.sub u) c (fun i V=> (hv i V).sub (hq i V)) hP
include hs hn
lemma penn (f f':F.Index→ Coin F Y Q)(x:F.Coeff): Swerve (breakP (pagesS Z K V f x) (pagesS Z K V f' x)) (pagesS Z K V (f-f') x) Y P:=by
   unfold pagesS; rw [← pencil_br]; unfold pencil; refine Swerve.mortar _ (fun i=>?_) Summable.of_finite Summable.of_finite (fun i V=>Summable.of_finite) (fun i V=>Summable.of_finite)
   dsimp only; rw [←turn_br]; exact Swerve.growing (Swerve.twist (points hf he h K hX i.2 (f i.2) (f' i.2)) _ (V i.1) _ hs hn) _
omit hs hn h hf he
-- independent primary integration.S integr.Sum helper.
lemma parish (j:F.Index)(f:Coin F Y Q): let H:= gather Z K (book (Size.axis F j) (Coin.uses f)) j
   breakP H (palmF Z K j f)=poseF Z j:=by
    intro S; let x:=tags Z K (book (Size.axis F j) (Coin.uses f)) j; let y:= dots Z K j f; let l:= stems Z j; let a(i):= Matric.tell (x i); let b(i):= Matric.tell (y i); let hY:= boom K hX j f
    have hT : Function.update y (.inl ()) (Z.main j)= x:=by ext1 i; rcases i with _|i|i <;> simp [x,y,tags,Function.update, consist]
    have hv : x=ᶠ[cofinite] y:=by rw [←hT]; filter_upwards [show ∀ᶠ i:I in cofinite, i≠.inl () from (Set.finite_singleton _).compl_mem_cofinite] with i hi; exact Function.update_of_ne hi _ _
    rw [show breakP S (palmF Z K j f)=_ from (melt (X:=a) (F':=b) (code _) ?_ hY.1 ?_ hY.2).symm]; unfold poseF
    · have hh(i):breakP (a i) (b i)=Matric.tell (l i):=by rw [show breakP (a i) (b i)=Matric.tell (x i-y i) from rfl,show x i-y i=l i from ?_]; rcases i with _|i|i; exact sub_zero _; exact sub_self _; exact sub_self _
      rw [show (fun i=> breakP (a i) (b i))= _ from funext hh]
    · exact hY.1.congr_cofinite (hv.symm.fun_comp (fun v=>(Matric.tell v).x))
    intro i V; exact ((hY.2 i V).congr_cofinite (hv.symm.fun_comp (fun v=> (Matric.tell v).forced i V)))
lemma splitS (f:F.Index→ Coin F Y Q)(w:F.Coeff): breakP (fullF Z K V f w) (pagesS Z K V f w)= pagesP Z V w:=by
   let ψ:= pagesP Z V w; unfold fullF pagesP pagesS; rw [←pencil_br]; apply congr_arg (fun i=> pencil (code _) i (chips F) w); funext i; rw [← turn_br]; exact congr_arg _ (parish K hX i.2 (f i.2))
omit hX
lemma sharedF (f:F.Index→ Coin F Y Q)(w:F.Coeff): (fullF Z K V f w).support=(pagesS Z K V f w).support:=by
   funext i; let j:= (code (Tally F)) i|>.1; exact congr_fun (turn_same (gather Z K (book (Size.axis F j.2) (Coin.uses (f j.2))) j.2) (palmF Z K j.2 (f j.2)) _ (V j.1) rfl) ((code (Tally F)) i|>.2)
lemma sharedP (f f': F.Index→ Coin F Y Q)(w:F.Coeff): (pagesS Z K V f w).support=(pagesS Z K V f' w).support:=by
   funext i; let j:= (code (Tally F)) i|>.1; exact congr_fun (turn_same (palmF Z K j.2 (f j.2)) (palmF Z K j.2 (f' j.2)) _ (V j.1) rfl) ((code (Tally F)) i|>.2)
end YM.FullVolume.Paint.Tower
