import YM.WilsonBulk.Staves.Loom
import YM.WilsonBulk.Staves.Muster

/-!
# Infinitesimal needle insertion at `SELF` interaction Tape. Orthogonality
   not postulated per order for V_e, only implies closed up-to-lower grades.
   KEEP Θ-independent real P and Leg references. z=(A,b) all colors and sites
   including flat mode and any signed. Supports all leg templates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Lattice Laurent Function Filter Bloch Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset Equiv
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {α β : Type} {G : Gauge} {i j : G.ColorIndex}
variable {c : Side} {f g : Flap}

-- map a stump to endpoints (axis/origin and fine wrap). Same axis read every color, site stencil vac (!)
attribute [local instance] Gauge.frobInner
abbrev Foot (G : Gauge) (n : Side) := Chamber (Pennant G n) (Atelier.Needle G n)
def lastAt (v : Site c × PotentialForm) (p : Bool) := if p then v.1+step (axisEquiv.symm v.2) else v.1
def booth (x : Site c) (i : G.ColorIndex) : Foot G c := Sum.inr (x,vac,i)
def opening (v : Site c × PotentialForm) (k : Boot G) : Foot G c := k.elim (fun i=> Sum.inl (selvedge v i)) (fun z=>booth (lastAt v z.1) z.2)
def sentence (v : Site c × PotentialForm) (i : G.ColorIndex) := flash (jack i ∘ socket (opening v))
lemma reading_jack (v : Site c×PotentialForm) (a : G.ColorIndex) (z : Tabletop (Foot G c)) : pigment c (1:G.El) z (selvedge v a)=jack a (socket (opening v) z) := by
  unfold pigment Function.comp cloakK narrative Lattice.gauge jack meadow
  rw [show selvedge v a=FreeResolvent.ix v a from rfl,← traces_at (v:=(traces G c 1).symm _) (i:=v) a] -- perhaps RHS not matching ix
  simp only [curtainK, one_mul, signal_at, ← coord_map, axisEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply, Work.F03.exp_neg_color]; simp; rfl
lemma plays_jack (v : Site c × PotentialForm) (k : G.ColorIndex) : exposure (pigment c 1) (selvedge v k)= submit (named ∘ opening v) (flash (jack k)) := by
  unfold exposure; rw [show (fun z=> pigment c (1:G.El) z (selvedge v k))=jack k ∘ socket (opening v) from funext fun z=> reading_jack ..,flash_comp (jack_height k) (jack_zero k) (socket _).contDiff.contDiffAt (map_zero _),expose_socket]

-- at site origin freeze b
abbrev demure (G : Gauge) (c : Side) (x : Interface G c) : Tabletop (Foot G c) := Sum.elim x 0
def nullify (G : Gauge) (c : Side) := submit (Sum.elim (named (α:=Pennant G c)) (0 : Atelier.Needle G c →Tape (Pennant G c)))
lemma nullify_tag (t : Atelier.Needle G c) : nullify G c (named (Sum.inr t))=0 := submit_named ..
lemma nullify_kind (t : Pennant G c) : nullify G c (privateName t)=named t := submit_named ..
lemma demure_pos : ContDiff ℝ ω (demure G c) := by apply contDiff_pi.mpr; rintro (i|i); exacts [contDiff_apply ℝ ℝ _,contDiff_const]
lemma demure_zero : demure G c 0=0 := by ext1 i; cases i <;> rfl
lemma demure_pulls : submit (exposure (demure G c))=nullify G c := by unfold nullify; congr 1; ext1 i; cases i; exacts [flash_named _,flash_0]
lemma nullified (u : Tape (Pennant G c)) : nullify G c (submit (exposure (pigment c (1:G.El))) u)=u := by
  rw [← demure_pulls, exposure_encode demure_pos.contDiffAt (pigment_jet _) demure_zero (pigment_birth _)]
  have he : pigment c (1:G.El) ∘ demure G c=ᶠ[𝓝 0] id:= cloakK_tip.mono fun z hz=> by
    rw [Function.comp_apply,pigment, Function.comp_apply, narrative, lower_both,upper_both, curtainK_zero]; change cloakK c (Lattice.gauge 1 _) = z; rw [turn_person]; exact hz
  rw [expose_match he,exposure_id,submit_id]
lemma adopt (v : Site c × PotentialForm) (A : Tape (Boot G)) :
    nullify G c (submit (named ∘ opening v) A) = submit (named ∘ selvedge v) (submit (exposure (walkway (G:=G))) A) := by
  let U:= (Sum.elim (named (α:=Pennant G c)) (0 : Atelier.Needle G c →Tape (Pennant G c)))
  let Y: Boot G→ Tape G.ColorIndex:=Sum.elim named 0
  have he : exposure (walkway (G:=G))=Y:=walkway_expose
  have hv (u : Boot G) : submit U (named (opening v u))=submit (named ∘ selvedge v) (Y u) := by
    cases u with
    | inl i=> change nullify G c (privateName (selvedge v i))=submit (named ∘ selvedge v) (named i); rw [nullify_kind,submit_named,Function.comp_apply]
    | inr i=> change nullify G c (named (Sum.inr (lastAt v i.1,vac,i.2))) = submit (named ∘ selvedge v) (0 : Tape G.ColorIndex); rw [nullify_tag,map_zero]
  change submit U _= _; rw [submits,he,submits]; exact congr_arg (fun u:Boot G→Tape (Pennant G c)=>submit u A) (funext hv)
lemma issuing (v : Pennant G c) (x : Site c) (i : G.ColorIndex) :
    nullify G c (player (booth x i) (exposure (pigment c (1:G.El)) v))=∑ t:Bool, if x=lastAt (fret v) t then submit (named ∘ selvedge (fret v)) (motive t v.2.2 i) else 0 := by
  rcases v with ⟨v,j,k⟩; let P:=(v,j)
  rw [show exposure (pigment c 1) (v,j,k)= _ from plays_jack P k,player_chain, Fintype.sum_sum_type]; simp only [map_add, map_mul, map_sum]
  -- tag matching, collisions contribute twice
  unfold opening; simp only [Function.comp_apply,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type]
  simp_rw [booth, player_name, apply_ite (nullify G c),map_one,map_zero]
  simp only [Sum.inl_ne_inr, ↓reduceIte,mul_zero,sum_const_zero, zero_add,Sum.inr.injEq,Prod.mk.injEq,true_and]; refine sum_congr rfl fun t _=> ?_
  rw [sum_eq_single i]
  · simp only [and_true, mul_ite,mul_one,mul_zero]; rw [motive_player, ← walkway_expose]; by_cases h:x=lastAt P t
    · rw [if_pos h.symm, if_pos h,← adopt]; rfl
    rw [if_neg (Ne.symm h),if_neg h]
  · intro a _ he; simp [he]
  simp
lemma declaration (V : Tape (Pennant G c)) (x : Site c) (i : G.ColorIndex) (h : Dances V) :
    (∑ y,∑ t: Bool, if x=lastAt (fret y) t then player y V* submit (named ∘ selvedge (fret y)) (motive t y.2.2 i) else 0)=0 := by
  let j:=booth x i
  have he:= h (1:G.El)
  have hx:= congr_arg (fun p=> nullify G c (player j p)) he; rw [player_chain] at hx
  have hm (t : Tape (Pennant G c)) : player j (mountain (Pennant G c) (Atelier.Needle G c) t)=0:= by rw [mountain,player_chain]; simp [j,booth,privateName]
  simp only [hm,map_zero,map_sum,map_mul,nullified,j,issuing, Finset.mul_sum, mul_ite, mul_zero] at hx; exact hx
end Parapet
end YM.WilsonBulk
