import YM.FullVolume.Reel.Fleet
/-!
# Narrowing multi.E Rotor

TOTAL X may include missing active wings (even for a zeros core chart, e.g. f=0 trivial returns Empty). Eligibility must be proven at ANY pose. NO read log contribution off the Mask.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f: Side}{E:Rep G c}{R:Rep G f}{o:Site f}{p:Site c}
variable {D:GaugeDoor R E}{X:Set Wing}
variable {β: Res G c}{α: Config G f→ℂ}{ζ: Res G f}{v δ:ℂ}{t u:ℝ}
variable {y: Essence G f}{x: Response G c}
variable {I:Type}{S:StepData c f}
open Menu YM.Merge YM.MergeProof.Menu
-- avoid DecEq.X mismatches. keep arbitrary gauge variable phase. Outside no occupancy.
def bornX (j:Wing)(h:j.blank R):Leaf R:= ⟨j,fun _=>0,fun _ _ _ _=>rfl,fun _ hi=> (hi rfl).elim,h,0,fun _=> norm_zero.le,fun _ _=>rfl,measurable_const⟩
abbrev prizes (i:Bool):ℂ:= if i then 1 else Complex.I
def sides (i:Bool): ℂ→L[ℝ] ℝ:= if i then Complex.reCLM else Complex.imCLM
lemma prizes_one (i:Bool) : ‖prizes i‖=1:= by cases i <;>simp [prizes]
lemma sidePrice (i:Bool)(x:ℂ): ‖sides i x‖≤‖x‖:=by cases i; exact Complex.abs_im_le_norm _; exact Complex.abs_re_le_norm _
section fuse
variable (Q:I→Leaf R)(r:I→ℂ)(s:Wing)(q: Config G f→ℂ)(h:∀ i,(Q i).turn=s) (hu:∀ U,∑' i:I, r i*((Q i).ingredient U:ℂ)=q U)
include Q r hu
lemma stere (hp:Summable (fun i=> ‖r i‖*(Q i).weight))(u:Bool)(M:Leaf R)(hM:Grouped M (fun i=> sides u (r i)) Q) : M.ingredient=fun U=> sides u (q U):=by
    funext U; rw [← hu U]
    let f(i):= r i*((Q i).ingredient U:ℂ); have he: Summable f:=hp.of_norm_bounded (fun i=> by unfold f; rw [norm_mul,Complex.norm_real]; exact mul_le_mul_of_nonneg_left (Leaf.earn ..) (norm_nonneg _))
    have hx:= (sides u).hasSum he.hasSum; refine (hM.earn U).unique (hx.congr_fun (fun i=>?_)); unfold f; rw [mul_comm (r i),← Complex.real_smul,map_smul]; exact mul_comm ..
omit hu
omit Q in
private lemma mingle {Z:I→ℂ}{a b:ℂ}(hr:HasSum (fun i=>(↑(r i).re:ℂ)*Z i) a)(hi:HasSum (fun i=>(↑(r i).im:ℂ)*Z i) b) : HasSum (fun i=> r i*Z i) (a+Complex.I*b):= (hr.add (hi.mul_left _)).congr_fun (fun i=> by nth_rw 1 [← Complex.re_add_im (r i)]; ring)
include h
lemma arrange [Countable I] (hw:Summable fun i=> ‖r i‖*(Q i).weight) (u:Bool)(hx:s.blank R): ∃ M:Leaf R,M.turn=s ∧ Grouped M (fun i=> sides u (r i)) Q:=by
    cases isEmpty_or_nonempty I
    next=> exact ⟨bornX s hx,rfl,fun i=>isEmptyElim i, Summable.of_finite, fun i=> show HasSum (_) (0:ℝ) from by simp⟩
    next=>
       let p(i):=sides u (r i); have hr:= hw.of_nonneg_of_le (fun i=> mul_nonneg (norm_nonneg (p i)) ((Q i).profit)) (fun i=>mul_le_mul_of_nonneg_right (sidePrice u _) ((Q i).profit)); obtain ⟨M,hM,he,h⟩:=squash Q s h p hr; exact ⟨M,he,hM⟩
omit h
lemma pressureZ [Countable I] (S:StepData c f) (T:GaugeDoor R E)(he:Tunes T)(hp:SoundDoor S T)(M:Bool→Leaf R) (hM:∀ u, Grouped (M u) (fun i=> sides u (r i)) Q):let f:= fun i:Bool=>prizes i
   (∀ U,HasSum (fun i=> r i*prose (Q i) U) (∑ i,f i*prose (M i) U)) ∧ (∀ i U,HasSum (fun j=> r j*entry (Q j) i U) (∑ j,f j*entry (M j) i U)) ∧∀ i U, HasSum (fun j=> v*r j*quoted T (Q j) i U) (∑ j,v*f j*quoted T (M j) i U):=by
    intro f
    refine ⟨fun U=>?_,fun i U=>?_,fun i U=>?_⟩
    · rw [Fintype.sum_bool]; simp only [f,prizes, Bool.false_eq_true,if_true,if_false,one_mul]; exact mingle r (Z:=fun i=> prose (Q i) U) (prose_me Q _ _ (hM true) U) (prose_me Q _ _ (hM false) U)
    · rw [Fintype.sum_bool]; simp only [f,prizes, Bool.false_eq_true,if_true,if_false,one_mul]; exact mingle r (Z:=fun j=> entry (Q j) i U) (entry_me Q _ _ (hM true) i U) (entry_me Q _ _ (hM false) i U)
    rw [Fintype.sum_bool]; simp only [f,prizes, Bool.false_eq_true,if_true,if_false,mul_assoc,one_mul,←mul_add]; exact (mingle r (Z:=fun j=> quoted T (Q j) i U) (tables T _ (hM true) he hp i U) (tables T _ (hM false) he hp i U)).mul_left _
end fuse
namespace Fleet
variable (h:Fleet R E D X o p v δ α ζ β t u y x)
include h
lemma compressP [Fintype X](he:Tunes D)(hp: SoundDoor S D)(hA:∀ i∈ X,i.blank R ∧ o∈ i.support R):∃ (Q:X × Bool→ Leaf R) (t':ℝ),Odyssey X o p v α ζ β δ t' u D Q (fun i=>prizes i.2) x ∧ (∀ i,(Q i).turn=i.1.val ∧ ∀ U,(Q i).ingredient U=sides i.2 (y i.1 U)) :=by
   obtain ⟨I,hI,M,r,h,H⟩:= h.buys; let a:I→ X:=fun i=>⟨(M i).turn,(h.member i).2⟩; let V(i:↥X):={j:I // a j=i}
   let u(i:↥X)(v:V i):= r v.val; let P(i:↥X)(v:V i):= M v.val; have hx : Summable (fun i=> ‖r i‖*(M i).weight):= weightFuse r M h.purchase
   have hz(i):Summable (fun j:V i=> ‖u i j‖*(P i j).weight):=hx.comp_injective Subtype.val_injective
   choose Q hQ hV using fun (i:↥X)(j:Bool)=> arrange (P i) (u i) i.val (fun v=> congr_arg Subtype.val v.property) (hz i) j (hA _ i.property).1
   let L(i:↥X × Bool):= Q i.1 i.2; let C₀(i:↥X × Bool):= ‖prizes i.2‖*load (L i)
   have HB (i:↥X):=(pressureZ (P i) (u i) (v:=v) S D he hp (Q i) (hV i)); have hB (f:I→ℂ) (p:X × Bool→ℂ)(s:ℂ)(h:HasSum f s) (hp:∀ i:↥X,HasSum (fun j:V i=> f j.val) (∑ j,p (i,j))): HasSum p s:=by
       have hh:= hasSum_fintype p; rw [Fintype.sum_prod_type] at hh; have he(i:↥X):∑ j,p (i,j)= cram a f i:= (hp i|>.tsum_eq).symm; simp_rw [he] at hh; have hr:∑ i,cram a f i = s:=by have hh:=(bulky a h.summable).tsum_eq.trans h.tsum_eq; rwa [tsum_fintype] at hh
       rw [hr] at hh; exact hh
   refine ⟨L,∑ i,C₀ i,⟨fun i=> ⟨?_,?_⟩,⟨fun i=>mul_nonneg (norm_nonneg _) ((L i).profit.trans (R.p.loMass _ _ (Leaf.profit (L i)))),Summable.of_finite, (tsum_fintype C₀).le⟩,h.cost,fun U=> hB _ _ _ (h.lyric U) (fun i=> (HB i).1 U),fun j U=> hB _ _ _ (h.old j U) (fun i=> (HB i).2.1 j U),fun j U=> hB _ _ _ (h.grants j U) (fun i=> (HB i).2.2 j U)⟩,?_⟩
   · change o∈ (Q i.1 i.2).turn.support R; rw [hQ]; exact (hA i.1.val i.1.property).2
   · exact (hQ i.1 i.2).symm ▸ i.1.property
   rintro ⟨i,j⟩; have ht(U):∑' v:V i,u i v*(((P i v).ingredient U:ℝ):ℂ)= y i U:=by
       rw [← (H i U).tsum_eq]; have he (v:V i): deposit r M U i v.val=u i v*((P i v).ingredient U:ℂ):= if_pos (show (M v.val).turn=i.val from congr_arg Subtype.val v.property)
       exact (tsum_congr (fun i' => (he i').symm)).trans (tsum_subtype_eq_of_support_subset (s:={j:I| a j=i}) (f:=deposit r M U i) (fun j hi=> by by_contra! h; exact hi (if_neg (show (M j).turn≠i.val from fun he=> h (Subtype.ext he)))))
   refine ⟨hQ i j,fun U=>?_⟩; exact congr_fun (stere (P i) (u i) (y i.val) ht (hz i) j (Q i j) (hV i j)) U
end Fleet
end YM.MergeProof.Matric
