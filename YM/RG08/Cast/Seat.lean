import YM.RG08.Cast.Troops

/-!
# Stable canonical base. Doesn't transport off-shell metric differences.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Cast
open Lattice Laurent Forms Pert.Bulk Isles Packets Carrel Filter Finset Function RG
open Anchor Rudder Rudder.Symmetry Exterior Stationary Bloch RG08.Flat Spar Next.Free Rows Bid Precision Loop
open scoped Topology ContDiff Classical BigOperators ENNReal Matrix
variable {G:Gauge}{σ C:ℝ}{P:Side}
local notation "o"=>(0:Fin 2)

/-- Need Sworn at arbitrary periods cofinal; `recognizable` transfers from stronger donors. -/
def root (G : Gauge)(B : Bed) := beam G (Flat.output B)
abbrev dye (G:Gauge):=Symmetry.dressed G 2
def funds (G:Gauge)(C:ℝ):ℝ:=tax G 1*(sumToken*(Fintype.card Faces*C))
theorem recognize (B:Bed){v:Clip}{τ u:ℝ}(hp:B.metric.strip σ C)(hb:∀ n,Floor B v n τ u)(h:∀ n,Sworn B n G)(ht:0<σ)(hi:σ≤1)(hc:0≤C): Spar.Ready (n:=1) (dye G) σ (funds G C) (Cast.root G B):=by
 let R:=plain B.metric; let F:=beam G R; let P:=Cast.root G B
 have he : Cast.root G B=picture G.ColorIndex 2 F:=podium _ hp hb hc ht hi
 obtain ⟨hf,hD⟩:=bearing (F:=F) Anchor.expand_grade
 have hb' := dressed_symm (G:=G) (N:=chain) (M:=fun i=> B.metric.acts (chain i)) (show Tendsto (fun i=>(chain i).val) atTop atTop by rw [tendsto_atTop_atTop];intro b; exact ⟨b,fun i hi=>by dsimp [chain];omega⟩) (fun i=>matches_plain _) (fun i=> (hb _).symmetric.1) (pass_one _) (plain0 hp le_rfl).1 ht hc
 let x:= Flat.output B; have hx := light_cities B
 obtain ⟨H,-⟩:=Flat.output_cost hp hc ht.le hi
 have hF:0 ≤ Flat.sumToken*(Fintype.card Faces*C):=mul_nonneg sumToken_pos (mul_nonneg (Nat.cast_nonneg _) hc)
 refine ⟨⟨Anchor.expand_path (spur_path (h:=hx)),Anchor.expand_grade,?_,?_,beam_hue⟩,he.symm ▸ hf, by unfold funds tax; positivity,Anchor.expand_cost (spur_cost H (from_row x hx H) hF ht.le)⟩
 · intro i;rw [he,←picture_woven];exact congrArg _ (hb' i)
 rw [he];exact oath G hp hb ht hc hi h

lemma adapts (G:Gauge)(B A:Bed){p:ℝ}(hs:0≤σ)(hp:0≤p)(h: RowCost σ 1 (Flat.output B-Flat.output A) p): Held (carpet _) σ (tax G 1*p) (Cast.root G B-Cast.root G A):=by
 have hc: city 1 (Flat.output B-Flat.output A):=fun i j v=>congrArg₂ (fun x y:ℝ=>x-y) (light_cities B i j v) (light_cities A i j v)
 rw [root,root,←beam_sub]
 exact Anchor.expand_cost (spur_cost h (from_row _ hc h) hp hs)

/-- `1/2` for all action terms because we use `parley`. Coordinates report **positive**
action Hessian if dividing deposited templates by `g²`. -/
def starter (G:Gauge)(B:Bed)(σ:ℝ):= (1/2:ℝ) • Spar.relift (n:=1) (dye G) σ (Cast.root G B)
lemma seats (B:Bed)(hG:G.Simple){v:Clip}{τ u θ L:ℝ}(hp:B.metric.strip σ C)(hb:∀ n,Floor B v n τ u)(h:∀ n,Sworn B n G)(ht:0<σ)(hi:σ≤1)(hc:0≤C)(hz:Rigged (n:=1) (dye G) σ θ L):
    let T:=starter G B θ
      ; Cloak (dye G) 2 T ∧ Held (carpet _) θ (L*funds G C) T ∧ picture G.ColorIndex 2 T=(1/2:ℝ) • Cast.root G B ∧ Loop.Core T (1/2):=by
 obtain ⟨hθ,-,hL,hx⟩:=hz
 obtain ⟨hr,hu,hf,-⟩:=hx (Cast.root G B) (funds G C) (recognize B hp hb h ht hi hc)
 let W:= starter G B θ
 have hW:Cloak (dye G) 2 W:=Loop.Cloak.smul hr (1/2:ℝ)
 have hcost:0≤funds G C:=by unfold funds tax; have :=sumToken_pos; positivity
 have he:Held (carpet _) θ (L*funds G C) W:=(hu.smul (1/2:ℝ)).mono le_rfl (mul_le_of_le_one_left (mul_nonneg hL hcost) (by norm_num)) (fun _=>le_rfl)
 intro T
 refine ⟨hW,he,by unfold T starter;rw [map_smul,←hf],?_⟩
 have ht' : Cast.root G B=picture G.ColorIndex 2 (beam G (plain B.metric)):=podium G hp hb hc ht hi
 let Y:=beam G (plain B.metric)
 have ha:= Anchor.expand_cost (spur_cost (G:=G) (plain0 hp le_rfl).1 (plain0 hp le_rfl).2 hc ht.le)
 convert Loop.plays (F:=W) hG hθ.le (mul_nonneg hL hcost) hW he using 1
 change _=Loop.measure ((1/2:ℝ) • _) hG
 rw [Loop.meter_scale, Loop.recognizes (F':=Y) hG hr.path (Anchor.expand_path (spur_path (pass_one _))) hθ (mul_nonneg hL hcost) ht (by unfold tax; positivity) hu ha (hf.symm.trans ht'),Loop.measured 1 hG (beam_core _ _ (hb (1:Side))),mul_one]
lemma seats_diff (A B:Bed){G:Gauge}{v:Clip}{τ u θ L p:ℝ}(hp:B.metric.strip σ C)(hp':A.metric.strip σ C)(hb:∀ n,Floor B v n τ u)(hb':∀ n,Floor A v n τ u)(h:∀ n,Sworn B n G)(h':∀ n,Sworn A n G)(ht:0<σ)(hi:σ≤1)(hc:0≤C)(hz:Rigged (n:=1) (dye G) σ θ L)(he: RowCost σ 1 (Flat.output A-Flat.output B) p)(hv:0≤p) :
   Held (carpet _) θ (L*(tax G 1*p)) (starter G A θ-starter G B θ):=by
 obtain ⟨hθ,-,hL,hx⟩:=hz
 have hs:=recognize A hp' hb' h' ht hi hc; have hB:=recognize B hp hb h ht hi hc
 have hE:0≤tax G 1*p:=by unfold tax; positivity
 obtain ⟨-,-,-,hf⟩:=hx _ _ hs
 have H:=hf (Cast.root G B) (funds G C) (tax G 1*p) hB hE (adapts G A B ht.le hv he)
 unfold starter; rw [← smul_sub];exact (H.smul (1/2:ℝ)).mono le_rfl (mul_le_of_le_one_left (by positivity) (by norm_num)) (fun _=>le_rfl)

theorem listens (B:Bed){v:Clip}{τ u θ L:ℝ}(hp:B.metric.strip σ C)(hb:∀ n,Floor B v n τ u)(h:∀ n,Sworn B n G)(ht:0<σ)(hi:σ≤1)(hc:0≤C)(hz:Rigged (n:=1) (dye G) σ θ L)(hG:G.Simple):
    pour (P:=P) (completed (starter G B θ) o 2) o =(1/2:ℝ) • arcade (Flat.quadratic B P):=by -- quadratic ambig
 obtain ⟨hW,he,hx,H⟩:=seats B hG hp hb h ht hi hc hz
 have ht':0 < θ:=hz.1
 have hc':0≤L*funds G C:=mul_nonneg hz.2.2.1 (by unfold funds tax; have :=sumToken_pos; positivity)
 rw [complete_top _ o hW he hc' ht',hx]
 have c_ear(F:Raw G.ColorIndex 2)(a:ℝ): pour (P:=P) (compress 1 (a • F)) o=a • pour (compress 1 F) o:=by
    ext z;rw [Pi.smul_apply,pour_at,pour_at];change (∑' x:Isles.lantern o z,a*compress 1 F x.val)=a*(∑' x:Isles.lantern o z,_);rw [tsum_mul_left]
 rw [c_ear,root, beam, show compress 1 (Anchor.extend 1 (spur G (Flat.output B)))=spur G (Flat.output B) from funext (fun j=>extend_top ..), spur_matches ((Flat.output_cost hp hc ht.le hi).2 P)]
end YM.RG08.Cast
