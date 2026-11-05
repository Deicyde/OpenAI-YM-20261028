import YM.RG08.Spar.Overhead

/-! Explicit solved unchanged-component gain AND alignment cost
before each and any repeated vacuum L. At varying widths. Consumers have to supply
that this *literal evaluated tensor equality holds* in the declared formal algorithm;
for forcing terms expressed jointly in chart variables prove that by integration,
packing and Ward, *not* by simply supplying two representatives with this difference.
-/
noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry Loop
open scoped Topology BigOperators Classical ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}{n:ℕ}{θ v σ ω C Q A:ℝ}{L:Side}{V:Submodule ℝ (Urn I (n+1))}{K:Kernel (TypeFace 2) (TypeFace 2)}

variable [Fintype I]

def stern (I:Type)[Fintype I](n:ℕ)(A v:ℝ):ℝ:=flashes I n (2*v)*(Fintype.card (Kind I 2)*A)^n
structure Blocks (s v ω:ℝ)(n:ℕ)(L:Side) : Prop where
 light : 0<v
 pin:4*v≤ω
 cargo : n*(4*v)≤ω
 tail : 4*v≤ (L.val:ℝ)*(s/n)

/-- Here and below i+1 finer width σ, v at coarser level chosen to fit under palette
NEEDED ON THIS step (not the palette of the coarser step alone), θ from warehouse at v. Gate
`Q*stern … ≤ L`: all L powers spent beforehand, so this doesn't consume γ iteratively.
Scalar old cost C at *the same* aperture σ finer is admitted; compare lift-choice differences
also at this gain (independent choices in the dark subspace would break this assertion). -/
theorem charter {F H Y:Raw I (n+1)} (hn:2≤n)(hs:0≤σ)(hp: Rigged V v θ Q) (hv:Atlas ω L 2 K A)(hK:city L K)(ho:Blocks σ v ω n L)(hL:Q*stern I (n+1) A v≤ L.val)
 {P:Raw I (n+1)} (hb:0≤C)(hf:Forms.Sym P)(hx:Cohort P)(hP:Held (carpet (Tone I)) σ C P)
 {p₁ p₂ B:ℝ}(hF:Ready V v p₁ F)(hH:Ready V v p₂ H)
 (heq:F-H=voucher K P+Y)(hY:Held (carpet (Tone I)) v B Y)(hB:0≤B):
 Held (carpet (Tone I)) θ (C/L.val+Q*B) (relift V θ F-relift V θ H) := by
 have ht:=lined hv hK hf hx hP hn hb hs v ho.light ho.pin ho.cargo ho.tail
 change Held _ v (stern I (n+1) A v*C/L.val^2) (voucher K P) at ht
 let c:=stern I (n+1) A v
 have hc:0≤c:=by unfold c stern;have he:=hv.nonneg; have hf:= flame_pos (I:=I) (n:=n+1) (by have hz:=ho.light;exact show (0:ℝ)<2*v by positivity) (by omega);positivity
 have hq:0 ≤ c*C/(L.val:ℝ)^2:= by positivity
 apply ((hp.2.2.2 F p₁ hF).2.2.2 H _ _ hH (add_nonneg hq hB) (by rw [heq];exact ht.add hY hq hB)).mono le_rfl ?_ (fun _=>le_rfl)
 rw [mul_add];gcongr -- goal C div
 have he:0<(L.val:ℝ):=by exact_mod_cast L.pos
 calc
 _ = Q*c*C/(L.val:ℝ)^2:=by ring
 _ ≤ (L.val:ℝ)*C/L.val^2:= by gcongr
 _ = _:=by field_simp

/-- Pair variant WITH uncertain kinetic base and quadratic reset after reclosure.
`T T'` input here represent the prescribed next base Hessian on curvature variables (or as
in density sign uses): give them prelength price ≤B because may be multiplied on same component,
variation D can be paid post-length. Normalization constant `s` is in SAME convention.
-/
def chargePair (I:Type)[Fintype I](A v σ:ℝ):ℝ:=let t:ℝ:=Fintype.card (Kind I 2);flashes I 2 (2*v)*(t*A*(t*(2/σ)*A))

theorem charter_pair {G:Gauge}(hΓ:G.Simple)(s:ℝ)(hS:s≠0){F H Y:Raw G.ColorIndex 2}{T T':Raw G.ColorIndex 2}
 (hs:0<σ)(hp:Rigged (n:=1) (Symmetry.dressed G 2) v θ Q) (hv:Atlas ω L 2 K A)(hK:city L K)
 (hr:0<v)(hD:4*v≤ω)(hw:8*v≤L.val*σ)
 -- expenditure illustration (reserve L^-1/2 gain without square-root API: use L^{1/2}, proven Stark)
 {B S P₁ P₂ D:ℝ}(B₀:ℝ)(_h₀:0≤B₀)(hL:(1+B/|s|)*Q*chargePair G.ColorIndex A v σ≤B₀)
 {P:Raw G.ColorIndex 2}(hb:0≤C)(hf:Forms.Sym P)(hx:Cohort P)(hT:Core P 0)(hP:Held (carpet (Tone G.ColorIndex)) σ C P)
 (hF:Ready (n:=1) (Symmetry.dressed G 2) v P₁ F)(hH:Ready (n:=1) (Symmetry.dressed G 2) v P₂ H)
 (heq:F-H=voucher K P + Y)(hY:Held (carpet (Tone G.ColorIndex)) v S Y)(hy:0≤S)
 (he:Held (carpet (Tone G.ColorIndex)) θ B T')(hk:Held (carpet (Tone G.ColorIndex)) θ B T)(hm:Held (carpet (Tone G.ColorIndex)) θ D (T-T'))(hB:0≤B)(hd:0≤D):
 let U:=relift (n:=1) (Symmetry.dressed G 2) θ F
 let U':=relift (n:=1) (Symmetry.dressed G 2) θ H
 -- Read ratio error separately (strict-only toward future positive orders)
 |Loop.reading U hΓ s-Loop.reading U' hΓ s| ≤ Q*(chargePair G.ColorIndex A v σ*C/L.val+S)/|s| ∧
 Held (carpet (Tone G.ColorIndex)) θ (B₀*C/L.val+(1+B/|s|)*Q*S+Q*P₁/|s| *D)
         (Loop.patch U T hΓ s - Loop.patch U' T' hΓ s):=by
 intro U U'
 have haveht:=leads hv hK hf hx hT hP hb hs v hr hD hw
 let c:= chargePair G.ColorIndex A v σ
 change Held _ v (c*C / L.val) _ at haveht
 have hc:0≤c:=by
   unfold c chargePair;dsimp only; have he:=flame_pos (I:=G.ColorIndex) (n:=2) (by nlinarith:0<2*v) (by omega); have hz:=hv.nonneg; positivity
 have hW:0≤ c*C/(L.val:ℝ):=by positivity
 have hx:=add_nonneg hW hy
 let t:=Q*(c*C/(L.val:ℝ)+S)
 have ht:Held (carpet _) θ t (U-U'):= (hp.2.2.2 _ _ hF).2.2.2 _ _ (c*C/(L.val:ℝ)+S) hH hx (by rw [heq]; exact haveht.add hY hW hy)
 have hQ:=hp.2.2.1;have h1:=mul_nonneg hQ hF.pos; have h2:=mul_nonneg hQ hH.pos
 obtain ⟨a,b⟩:=patch_variation hΓ s hS θ _ _ _ _ _ _ hp.1 h1 h2 hB (mul_nonneg hQ hx) hd ((hp.2.2.2 F P₁ hF).2.1) ((hp.2.2.2 H P₂ hH).2.1) hk he ht hm
 refine ⟨a,b.mono le_rfl ?_ (fun _=>le_rfl)⟩
 rw [show Q*(c*C/↑L.val+S)+Q*(c*C/↑L.val+S)/|s| *B = (1+B/|s|)*Q*c*C/↑L.val+(1+B/|s|)*Q*S by ring];gcongr
end YM.RG08.Spar
