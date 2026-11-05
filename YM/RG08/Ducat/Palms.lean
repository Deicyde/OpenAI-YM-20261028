import YM.RG08.Ducat.Scrap

/-! # Canonical repeated licenses stated before length in all lane factors. -/
noncomputable section
namespace YM.RG08.Ducat
open Packets Filter Function Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry
open scoped Classical BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}(hg:G.Simple){O:Type}{D:Exchange O}{d:O→ℝ}{r e:ℕ}
variable {ω X L b v s B q:ℝ}{M:Kernel (TypeFace 2) (TypeFace 2)}
private lemma hz_pos (n:ℕ)(x v:ℝ)(hv:0<v)(hx:0≤x): 0 ≤ stern G.ColorIndex (RG08.Mount.rank n) x v:=by unfold stern; exact mul_nonneg (flame_pos (by positivity) (Nat.zero_lt_succ _)) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hx) _)
private lemma hx_pos (x v s:ℝ)(hv:0<v)(hs:0<s)(hx:0≤x):0 ≤ chargePair G.ColorIndex x v s:=by unfold chargePair; have he:=flame_pos (I:=G.ColorIndex) (by positivity: (0:ℝ)<2*v) (by decide:0<2);simp only; positivity

def coin (G:Gauge)(r:ℕ)(x v s:ℝ):= if r=0 then Spar.chargePair G.ColorIndex x v s else Spar.stern G.ColorIndex (RG08.Mount.rank r) x v
lemma coin_nn (n:ℕ)(x v s:ℝ)(hv:0<v)(hs:0<s)(hx:0≤x):0 ≤ coin G n x v s:=by unfold coin; split; exact hx_pos _ _ _ hv hs hx;exact hz_pos _ _ _ hv hx
structure Innate (s v w:ℝ)(r:ℕ)(L:Side):Prop extends Blocks s v w (r+1) L where
 extra:8*v≤L.val*s
structure Royal (G:Gauge)(H:Yard G)(X s B ω:ℝ)(r e:ℕ)(L:Side) : Prop where
 cargo:Innate s (H.need e r) ω r L
 posB:0 ≤ B
 posX:0 ≤ X
 enter: (1+2*B)*(H.cash e r)*coin G r X (H.need e r) s ≤ Real.sqrt (L.val:ℝ)

/-- On positive rank zero Core and Holder actual prices. The coarse base normalization support
 price B must be a *prelength* constant, although its variation may be post. -/
structure Native (G:Gauge)(P:Gird G r)(s C:ℝ):Prop where
 held: Held (carpet _) s C P
 known: Sym P
 town: Cohort P
 root: if h:r=0 then Loop.Core (h ▸ P) 0 else True
lemma currency {Φ:Gird G r}{l: Side}(h:Atlas ω l 2 M X)(hh:city l M)(he:Native G Φ s q)(hs:0<s)(hb:Innate s v ω r l)(hq:0≤q):Held (carpet _) v (coin G r X v s*q / l.val) (voucher M Φ):=by
 rcases eq_or_ne r 0 with hr|hr
 · subst r; unfold coin;rw [if_pos rfl];exact leads h hh he.known he.town (show Loop.Core Φ 0 from he.root) he.held hq hs _ hb.light hb.pin hb.extra
 rw [coin,if_neg hr]
 apply (lined h hh he.known he.town he.held (by omega: 2 ≤ r+1) hq hs.le v hb.light hb.pin hb.cargo hb.tail).mono le_rfl _ (fun _=>le_rfl)
 have hp:= mul_nonneg (hz_pos (G:=G) r X v hb.light h.nonneg) hq
 change stern G.ColorIndex _ _ _ * q /_ ≤ _
 have hl:1 ≤ (l.val:ℝ):=Nat.one_le_cast.mpr l.property
 gcongr _ / ?_ ; nlinarith

-- normalization for repeated r.
def vac (S:Gird G 0) (F:Gird G r): Gird G r := F- if h:r=0 then h ▸ (Loop.reading (cast (congrArg (Gird G) h) F) hg (1/2) • S) else 0
lemma victim_r (A:Castle G)(r e:ℕ): victim hg A r e=vac hg (A 0 0) (A r e):=by unfold victim vac;split <;> rename_i he;subst r;rfl;rfl
variable {F T Y P:Gird G r}
lemma waxed (hg:G.Simple){σ s w q x y a z : ℝ}{l:Side}(H:Yard G)(h:Royal G H x σ z w r e l)(hL:Atlas w l 2 M x)(hM:city l M)(hσ:0<σ)
 (hF:Ready (n:=r+1) (Symmetry.dressed G (RG08.Mount.rank r)) (H.need e r) s F)(hT:Ready (n:=r+1) (Symmetry.dressed G (RG08.Mount.rank r)) (H.need e r) q T)
    (hEq:F-T=voucher M P+Y)(hY:Held (carpet _) (H.need e r) y Y)(hy:0 ≤ y)(hP:Native G P σ a)(hA:0≤a)
 {S S':Gird G 0}{c:ℝ}(hb:c≥0)(hp: r=0 → Held (carpet (Tone _)) (H.coats e r) z S ∧ Held (carpet (Tone _)) (H.coats e r) z S' ∧ Held (carpet (Tone _)) (H.coats e r) c (S-S')):
 let U:= grant H e F; let U':= grant H e T
 ; let t:= coin G r x (H.need e r) σ
 ; Held (carpet _) (H.coats e r) (a/(Real.sqrt (l.val:ℝ))+(1+2*z)*H.cash e r*y+H.cash e r*s*2*c) (vac hg S U-vac hg S' U') ∧ Held (carpet _) (H.coats e r) (H.cash e r*(t*a/l.val+y)) (U-U'):=by
 intro U U' t
 unfold U U';rw [grant_open _ _ _ hF.held,grant_open _ _ _ hT.held]
 have hx:0 < (l.val:ℝ):=Nat.cast_pos.mpr l.property
 have hθ:= H.tall e r
 obtain ⟨hU,-,hV,Ht⟩:=H.tag e r
 have hL':0 ≤ t:=coin_nn _ _ _ _ hθ hσ h.posX
 let W:=relift (n:=r+1) (Symmetry.dressed G (RG08.Mount.rank r)) (H.coats e r) F
 let W':=relift (n:=r+1) (Symmetry.dressed G (RG08.Mount.rank r)) (H.coats e r) T
 obtain ⟨hc,hf,-,HH⟩:=Ht F s hF
 let v:=t*a/l.val+y;have hv:0≤v:=add_nonneg (div_nonneg (mul_nonneg hL' hA) hx.le) hy
 have ht: Held (carpet _) (H.coats e r) (H.cash e r*v) (W-W'):= HH T _ v hT hv (by rw [hEq]; exact (currency hL hM hP hσ h.cargo hA).add hY (div_nonneg (mul_nonneg hL' hA) hx.le) hy)
 refine ⟨?_,ht⟩
 have he:(1+2*z)*(H.cash e r*v)+H.cash e r*s*2*c≤a/Real.sqrt (l.val:ℝ)+(1+2*z)*H.cash e r*y+H.cash e r*s*2*c:=by
    have hT:(1+2*z)*H.cash e r*t ≤ Real.sqrt (l.val:ℝ):=h.enter
    suffices hv:(1+2*z)*H.cash e r*t*a/(l.val:ℝ) ≤ a/Real.sqrt (l.val:ℝ) by unfold v; simp only [div_eq_mul_inv] at *; nlinarith only [hv]
    refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hT hA) hx.le).trans (le_of_eq ?_)
    have hh:Real.sqrt (l.val:ℝ)≠0:=(Real.sqrt_pos.mpr hx).ne'
    field_simp; rw [Real.sq_sqrt hx.le];ring
 rcases eq_or_ne r 0 with hr|hr
 · subst r;obtain ⟨hG,hG',hC⟩:=hp rfl
   have hd:Held (carpet _) (H.coats e 0) (H.cash e 0*v+H.cash e 0*v/|(1/2:ℝ)| *z+H.cash e 0*s/|(1/2:ℝ)| *c) (Loop.patch W S hg (1/2)-Loop.patch W' S' hg (1/2)):= (patch_variation hg _ (by norm_num) _ (H.cash e 0*s) (H.cash e 0*q) z z (H.cash e 0*v) c hU (mul_nonneg hV hF.pos) (mul_nonneg hV hT.pos) h.posB (mul_nonneg hV hv) hb hf ((Ht T q hT).2.1) hG hG' ht hC).2
   exact hd.mono le_rfl (by norm_num; nlinarith only [he]) (fun _=>le_rfl)
 unfold vac;rw [dif_neg hr,dif_neg hr,sub_zero,sub_zero];exact ht.mono le_rfl ((show H.cash e r*v ≤ (1+2*z)*(H.cash e r*v)+H.cash e r*s*2*c by have hx:= h.posB; have hs:= hF.pos; nlinarith [mul_nonneg (mul_nonneg hV hv) hx,mul_nonneg (mul_nonneg hV hs) hb]).trans he) (fun _=>le_rfl)
end YM.RG08.Ducat
