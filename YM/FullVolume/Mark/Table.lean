import YM.MergeProof.Meringue
/-!
# Source coupons, one fixed common notation at each level.

Different from the vacuum's label conventions: regular supports in the
*same* period but may attach to different inputs in the fixed-point estimate;
need arbitrary many copies per support. Never combine countably many regular
entries sharing just support (would need germ smoothness off Healthy!).
Tab tracks turn-purchases before projection and after mounting reexpression on
a Born column. `Fire`'s κ is a fixed forced divisor, only on this timestamp.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}
def mapSeat (s:ℕ):Support n:= insert 0 (code (Support n) s).1
lemma spot (n:Side)(s:ℕ): (0:Site n)∈mapSeat s := mem_insert_self ..
abbrev File (G:Gauge)(n:Side):= (ℕ→ Config G n→ℂ)×(ℕ→ Config G n→ℂ)
def book (v:F.Coeff) (P:File G n) : Coefficient F n := ⟨v,mapSeat,P.1,P.2⟩
@[simp] lemma book_x (v : F.Coeff)(A:File G n) : (book v A).x=v:=rfl
@[simp] lemma bookK (v : F.Coeff)(A:File G n) : (book v A).forced=A.2:=rfl
@[simp] lemma bookE (v : F.Coeff)(A:File G n) : (book v A).regular=A.1:=rfl
@[simp] lemma bookS (v : F.Coeff)(A:File G n) : (book v A).support=mapSeat:=rfl
lemma stamp {P: Coefficient F n} (h:P.support=mapSeat): book P.x (P.regular,P.forced)=P:=by cases P; dsimp at *; subst_vars; rfl
variable (F) {R: Rep G n}{Y:Hol G}{κ: NNReal} -- avoid subtype positive H.
variable (u v:F.Coeff)
variable {P Q:File G n} {a b c e :ℝ}

lemma formatK (h : (book u P).Format 0 Y R) : (book v P).Format 0 Y R:= ⟨h.smooth,h.origin,h.identity_null,h.projects,h.forcing,h.carried,h.invariant,h.supported,h.borel⟩
lemma boundK {κ:ℝ} (h: (book u P).remBound 0 R κ a): (book v P).remBound 0 R κ a:= h
lemma format_add (h:(book u P).Format 0 Y R)(hx : (book v Q).Format 0 Y R): (book u (P+Q)).Format 0 Y R:=by
   have hp : ForceFormat R.p R.activities 0 (book u P).forced:= ⟨h.forcing,h.carried,h.invariant,h.supported,h.borel⟩
   have hq : ForceFormat R.p R.activities 0 (book v Q).forced:= ⟨hx.forcing,hx.carried,hx.invariant,hx.supported,hx.borel⟩
   have hh:= hp.add hq
   refine ⟨fun i=> regular_add (h.smooth i) (hx.smooth i), h.origin,fun i=>?_ ,fun i ht J=>?_, hh.forcing,hh.carried,hh.invariant,hh.supported,hh.borel⟩
   · change (book u P).regular i _ + (book v Q).regular i _ = 0; rw [h.identity_null,hx.identity_null,add_zero]
   obtain ⟨hb,hU⟩:=h.projects i ht J; obtain ⟨hb',hV⟩:= hx.projects i ht J; refine ⟨hb.add hb',fun k hk=> ?_⟩
   change iteratedDeriv k (fun r=> (book u P).regular i (Y.testLinks d 0 J r)+ (book v Q).regular i (Y.testLinks d 0 J r)) 0=0
   have he : (k:WithTop ℕ∞)≤(d:WithTop ℕ∞):=Nat.cast_le.mpr hk
   rw [iteratedDeriv_fun_add (hb.of_le he) (hb'.of_le he),hU _ hk,hV _ hk,add_zero]
lemma tally_add {κ:ℝ} (h:(book u P).Format 0 Y R)(hx : (book v Q).Format 0 Y R)(he:Tab (book u P) 0 R κ a b)(hu: Tab (book v Q) 0 R κ c e): Tab (book u (P+Q)) 0 R κ (a+c) (b+e):=by
   have hp := Local.ForceCost.add he.forced hu.forced; rw [← mul_add] at hp
   obtain ⟨f,hf,hb⟩:= he.regular; obtain ⟨g,hg,hc⟩:= hu.regular
   refine ⟨he.divisor, add_nonneg he.first hu.first,add_nonneg he.second hu.second,⟨fun i=>f i+g i,?_ ,fun i=> Next.Foundations.bound_add (h.smooth _) (hx.smooth _) (hb i) (hc i) ⟩,hp⟩
   let X i:=R.p.mass (mapSeat (n:=n) i) (f i); let Y' i:= R.p.mass (mapSeat (n:=n) i) (g i)
   have hx : (fun i=>R.p.mass ((book u (P+Q)).support i) (f i + g i))= X+Y':=by ext i; simp only [X,Y',bookS, Pi.add_apply,BudgetPoint.mass,mul_add]
   rw [hx]; exact ⟨fun i=>add_nonneg (hf.1 _) (hg.1 _),hf.2.1.add hg.2.1, (show Summable X from hf.2.1).tsum_add (show Summable Y' from hg.2.1) |>.trans_le (add_le_add hf.2.2 hg.2.2)⟩
lemma remAdd {κ:ℝ} (h:(book u P).Format 0 Y R)(hx : (book u Q).Format 0 Y R)(he:(book u P).remBound 0 R κ a)(hu:(book u Q).remBound 0 R κ c): (book u (P+Q)).remBound 0 R κ (a+c):=by
   obtain ⟨f,g,h₁,h₂⟩:= rem_tabs.mp he; obtain ⟨b,e,h₃,h₄⟩:= rem_tabs.mp hu
   exact (tally_add F _ _ h hx h₁ h₃).bound (by linarith only [h₂,h₄])
lemma disguise (s:ℂ)(u:F.Coeff)(P:File G n):Extra.Histories.stretch s (book u P)=book (s•u) (s•P):=rfl
section
-- Kernel of seminorm can include junk from unmasked extensions. Real-prescription outputs before completion.
variable (Y: Hol G)
structure Desk (G: Gauge)(n:Side) where
   orient: Rep G n
   k : ℝ
   sane : 0<k
abbrev Pay (S: Desk G n)(P:File G n)(q:ℝ): Prop:= (book (0:F.Coeff) P).Format 0 Y S.orient ∧ (book (0:F.Coeff) P).remBound 0 S.orient S.k q
def tent (S:Desk G n): Submodule ℂ (File G n) where
   carrier:= {P|∃ q, Pay F Y S P q}
   zero_mem':=by
      refine ⟨0,⟨fun i=> (regular0 S.orient.p (mapSeat i) 0).1,fun i=>spot n i,fun i=>rfl,fun i _=> vanishing0 _ _ Y,fun i U h=>False.elim (h rfl),fun i h=>False.elim (h rfl),fun _ _ _=>rfl,fun _ _ _ _ _=> rfl,fun _=>measurable_const⟩,0,0,le_rfl,le_rfl,(add_zero 0).le,S.sane,⟨0,budget0 ..,fun i=> (regular0 S.orient.p (mapSeat i) 0).2⟩,fun i=>0,?_,fun _=> ⟨le_rfl,fun U=> (norm_zero (E:=ℂ)).le⟩⟩
      rw [mul_zero]; exact budget0 ..
   add_mem' :=by
     intro x y ⟨b,hb,hf⟩ ⟨v,hv,hg⟩; exact ⟨b+v,format_add F _ _ hb hv, remAdd F _ hb hv hf hg⟩
   smul_mem' x _ h:= by
     obtain ⟨p,hp,hx⟩:= h; have hA:= stretch_format x hp; have hC:= stretch_rem x hx; rw [disguise,smul_zero] at hA hC; exact ⟨_,hA,hC⟩
end
end YM.MergeProof.Matric
