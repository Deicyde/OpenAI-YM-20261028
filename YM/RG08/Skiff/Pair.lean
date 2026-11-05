import YM.RG08.Skiff.Pocket
import YM.RG08.Forms.Cot

/-! # Cutoff differences on marked pairings -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Skiff
open Forms Pert.Bulk Jetty Function Finset
open scoped BigOperators Topology ENNReal Classical
variable {I:Type}{m n d:ℕ}{σ B C D δ:ℝ}{h:0<σ}{L:Loom I}{A:Ground I}
structure Dyad (L:Loom I)(d:ℕ)(h:0<σ)(B δ:ℝ)(F F':Pack n I):Prop where
 price : 0≤ B
 rate : 0≤ δ
 voices : Lyrics F ∧ Lyrics F'
 near : Sings L d h F B
 far : Sings L d h F' B
 switch : Sings L d h (F-F') (B*δ)
variable {F F' P P':Pack n I}
lemma Dyad.mono (hv:Dyad L d h B δ F F')(he:B≤C):Dyad L d h C δ F F':= ⟨hv.price.trans he,hv.rate,hv.voices,hv.near.mono le_rfl le_rfl (fun _=>le_rfl) he,hv.far.mono le_rfl le_rfl (fun _=>le_rfl) he,hv.switch.mono le_rfl le_rfl (fun _=>le_rfl) (mul_le_mul_of_nonneg_right he hv.rate)⟩
lemma Dyad.add (h₁:Dyad L d h B δ F F')(h₂:Dyad L d h C δ P P'):Dyad L d h (B+C) δ (F+P) (F'+P'):=by
 obtain ⟨hp,hδ,hv,he,hf,hs⟩:=h₁; obtain ⟨hq,_,hv',he',hf',hs'⟩:=h₂
 refine ⟨add_nonneg hp hq,hδ,⟨hv.1.add hv'.1,hv.2.add hv'.2⟩,he.add he' hp hq,hf.add hf' hp hq,?_⟩
 rw [add_sub_add_comm,add_mul];exact hs.add hs' (mul_nonneg hp hδ) (mul_nonneg hq hδ)
lemma Dyad.smul (h₁:Dyad L d h B δ F F')(a:ℝ):Dyad L d h (|a| * B) δ (a • F) (a • F'):=by
 obtain ⟨hp,hδ,hv,he,hf,hs⟩:=h₁
 refine ⟨mul_nonneg (abs_nonneg a) hp,hδ,⟨hv.1.smul a,hv.2.smul a⟩,he.smul a,hf.smul a,?_⟩
 rw [←smul_sub,mul_assoc];exact hs.smul a
lemma Dyad.zero (he:0≤δ):Dyad L d h 0 δ (0:Pack n I) 0:=⟨le_rfl,he,⟨hush,hush⟩,tin,tin,by rw [sub_zero];exact tin⟩
lemma Dyad.sum {T:Type}{C:T→ℝ}{F F':T→Pack n I}(s:Finset T)(he:∀ i∈s,Dyad L d h (C i) δ (F i) (F' i))(hδ:0≤δ):Dyad L d h (∑ i∈s,C i) δ (∑ i∈s,F i) (∑ i∈s,F' i):=by
 induction s using Finset.induction_on with
 | empty=>simp only [sum_empty]; exact Dyad.zero hδ
 | @insert i s hi ih=> simp_rw [sum_insert hi]; exact (he i (mem_insert_self ..)).add (ih fun i hi=>he i (mem_insert_of_mem hi))

private lemma breeze_add (F G:Pack n I):breeze (F+G)=breeze F+breeze G:=by unfold breeze;simp_rw [show (pattern (n:=n) · (F+G))=(fun i=>pattern i F+pattern i G) from rfl,sum_add_distrib,smul_add]
private lemma breeze_sub(F G:Pack n I):breeze (F-G)=breeze F-breeze G:=by unfold breeze;simp_rw [show (pattern (n:=n) · (F-G))=(fun i=>pattern i F-pattern i G) from rfl,sum_sub_distrib,smul_sub]

variable {Γ Γ':Forms.Line I}{H H':Pack (n+2) I}{Q Q':Pack (m+1) I}{Y Y':Flake (n+1) I}
private lemma vary_seed (x:Tape n I)(u:I×I)(f:Pearl): nut Γ H x u f-nut Γ' H' x u f=nut Γ (H-H') x u f+nut (Γ-Γ') H' x u f:=by unfold nut; simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul];ring
lemma Dyad.pocket (hv:Dyad L d h B δ H H')(hg:WireCot A σ δ C Γ Γ'):Dyad L d h (2*B*C) δ (pocket Γ H) (pocket Γ' H'):=by
 obtain ⟨hB,hδ,hv,ha,hb,hc⟩:=hv;have hC:= hg.near.gain
 obtain ⟨hn,hf⟩:= opening hB hv.1 ha hg.near;obtain ⟨hm,hm'⟩:=opening hB hv.2 hb hg.far
 have he:B*C≤2*B*C:= by nlinarith [mul_nonneg hB hC]
 refine ⟨(mul_nonneg hB hC).trans he,hδ,⟨hn,hm⟩,hf.mono le_rfl le_rfl (fun _=>le_rfl) he,hm'.mono le_rfl le_rfl (fun _=>le_rfl) he,?_⟩
 have hs:Skiff.pocket Γ H-Skiff.pocket Γ' H'= Skiff.pocket Γ (H-H')+Skiff.pocket (Γ-Γ') H':=by
   unfold Skiff.pocket; rw [← breeze_sub,←breeze_add];apply congrArg breeze; ext x f
   have hx {S:Forms.Line I}{F:Pack (n+2) I}{K M:ℝ}(hv:Wire A σ K S)(hP:Sings L d h F M)(hF:Lyrics F):Summable (fun u=>nut S F x u f):=((looted hv hP).deep (seed hF) x f).of_norm
   unfold decker;simp only [Pi.sub_apply,Pi.add_apply];rw [← (hx hg.near ha hv.1).tsum_sub (hx hg.far hb hv.2),← (hx hg.near hc (hv.1.sub hv.2)).tsum_add (hx hg.compare hb hv.2)];simp_rw [vary_seed]
 rw [hs]; convert (opening (mul_nonneg hB hδ) (hv.1.sub hv.2) hc hg.near).2.add (opening hB hv.2 hb hg.compare).2 (by positivity) (by positivity) using 1; ring
private lemma vary_sleeve (x:Tape (m+n) I)(u:I×I)(f:Pearl): sleeve Γ Q Y x u f-sleeve Γ' Q' Y' x u f=
    (sleeve Γ (Q-Q') Y x u f+sleeve (Γ-Γ') Q' Y x u f)+sleeve Γ' Q' (Y-Y') x u f:=by unfold sleeve; simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul];ring

lemma Dyad.cloak (ht:fits L A)(hv:Dyad L d h B δ Q Q')(hg:WireCot A σ δ C Γ Γ')(hi:Cot A σ δ D Y Y'):Dyad L d h (3*(B*C*D)) δ (cloak Γ Q Y) (cloak Γ' Q' Y'):=by
 obtain ⟨hB,hδ,hv,ha,hb,hc⟩:=hv;have hC:= hg.near.gain;have hD:=hi.gain
 obtain ⟨hn,hf⟩:= enrobes hB hD hv.1 ht ha hi.near hg.near;obtain ⟨hm,hm'⟩:=enrobes hB hD hv.2 ht hb hi.far hg.far
 have he:B*C*D≤3*(B*C*D):= by nlinarith [mul_nonneg (mul_nonneg hB hC) hD]
 refine ⟨(mul_nonneg (mul_nonneg hB hC) hD).trans he,hδ,⟨hn,hm⟩,hf.mono le_rfl le_rfl (fun _=>le_rfl) he,hm'.mono le_rfl le_rfl (fun _=>le_rfl) he,?_⟩
 have hs:Skiff.cloak Γ Q Y-Skiff.cloak Γ' Q' Y'=(Skiff.cloak Γ (Q-Q') Y+Skiff.cloak (Γ-Γ') Q' Y)+Skiff.cloak Γ' Q' (Y-Y'):=by
   unfold Skiff.cloak; rw [← breeze_sub,←breeze_add,←breeze_add];apply congrArg breeze; ext x f
   have hx {S:Forms.Line I}{Z:Flake (n+1) I}{F:Pack (m+1) I}{K M W:ℝ}(hv:Wire A σ K S)(hP:Sings L d h F M)(hy:Held A σ W Z)(hp:0≤M)(hF:Lyrics F):Summable (fun u=>sleeve S F Z x u f):=((jackets ht hP hy hv hp).deep (cuff hF) x f).of_norm
   have h₁:=hx hg.near ha hi.near hB hv.1; have h₂:=hx hg.far hb hi.far hB hv.2;have h₃:=hx hg.near hc hi.near (mul_nonneg hB hδ) (hv.1.sub hv.2); have h₄:=hx hg.compare hb hi.near hB hv.2;have h₅:=hx hg.far hb hi.compare hB hv.2
   unfold decker;simp only [Pi.sub_apply,Pi.add_apply];rw [← h₁.tsum_sub h₂,← h₃.tsum_add h₄,← (h₃.add h₄).tsum_add h₅];simp_rw [vary_sleeve]
 rw [hs]
 convert ((enrobes (mul_nonneg hB hδ) hD (hv.1.sub hv.2) ht hc hi.near hg.near).2.add (enrobes hB hD hv.2 ht hb hi.near hg.compare).2 (by positivity) (by positivity)).add (enrobes hB (mul_nonneg hD hδ) hv.2 ht hb hi.compare hg.far).2 (by positivity) (by positivity) using 1; ring
end YM.RG08.Skiff
