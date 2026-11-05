import YM.Push.RELAY_DIFFERENCE.Placement
import YM.UVExtension.Orchard.Vanilla
import YM.UVExtension.Hearth.Palms
import YM.Push.RELAY_MARK.Micro
/-! Full-sequence finite-period comparison for rooted powers with placements.
 All translated cylinders have both-end collars. Invisible parts omitted in
 complete correlation at the aperture itself, not divided individual
 seam norms. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Lattice Wilson RG Cells Extraction Push GridApprox Hearth
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {C:Schedule}{s:Side}{G:Gauge}{μ:Family G}{N p m n:ℕ}

-- cutoffs's family at ONE period
abbrev Stem (μ:Family G) (p:ℕ):= (N:ℕ) → Config G (μ.S.side N p)→ ℂ

def bloom {G:Gauge}{s:Side}(F:Config G s→ℂ)(o:Site s) : Config G s→ℂ:= F ∘ translate o
lemma literal (F:Config G s→ℂ): RelayDifference.literal (bloom F):=by
   intro a b; funext V; unfold bloom; dsimp only [Function.comp_apply]; congr! 1 -- translate commute
   funext i; change V (i.1+_,_)=V (_, _); dsimp only; rw [add_assoc]
lemma home (F:Config G s→ℂ): bloom F 0=F:=by funext x; apply congr_arg F; funext i; change x (i.1+ (0:Site s),i.2)=x i; rw [add_zero]

def Pasted (F:Stem μ p): Prop := ∃ r,∀ᶠ N in atTop,Interior (GridApprox.window 0 r) (F N)
namespace Pasted
variable {F V:Stem μ p}
lemma blast (h:Pasted F) : ∀ᶠ N in atTop,Envelope (F N):=by obtain ⟨r,hr⟩:= h; exact hr.mono fun n hn=>cylinder_env hn
lemma vistas (h:Pasted F)(m:ℕ): ∀ᶠ N in atTop, ∃ h:m≤N,Interior ((tilesAt μ.S p h).chamber 0) (F N):=by
   obtain ⟨r,hr⟩:=h; have he:= (plenty μ.path.levels m r)
   filter_upwards [hr,eventually_ge_atTop m,he] with N h hn hu; have he' : anchor μ.S p hn 0=0:= (μ.S.toDepth hn p).root.map_zero
   refine ⟨hn,h.enlarges ?_⟩;  have hh:= room_fits p μ.path.levels r hn le_rfl hu (0:Site (μ.side m p)); simp only [he',begin_radius] at hh; exact hh
lemma plus (h:Pasted F)(hp:Pasted V): Pasted (F+V):=by
   obtain ⟨r,hr⟩:=h; obtain ⟨k,hk⟩:=hp; exact ⟨max r k,(hr.and hk).mono fun n ⟨he,hh⟩=> (he.enlarges (window_large (le_max_left ..))).plus (hh.enlarges (window_large (le_max_right ..)))⟩
lemma smulT (h:Pasted F)(v:ℕ→ℂ) : Pasted (μ:=μ) (p:=p) (fun n=> v n • F n) := by
   obtain ⟨r,hr⟩:=h; exact ⟨r,hr.mono fun n hn=> hn.scale (v n)⟩
lemma subH (h:Pasted F)(hp:Pasted V): Pasted (F-V):=by
   rw [sub_eq_add_neg, ← neg_one_smul ℂ V]; exact h.plus (smulT hp _)
lemma nil : Pasted (0:Stem μ p):= ⟨0,Eventually.of_forall fun _=> Interior.constant ..⟩
end Pasted

def bills (F:Stem μ p)(m N:ℕ)(b:ℝ): Prop:=∀ h:m≤N,(tilesAt μ.S p h).rootTest (μ.beta N p) (F N) ≤ b

def Faded (μ: Family G)(F:Stem μ p): Prop := Pasted F ∧ ∀ᶠ j in atTop, ∀ ε:ℝ,0 < ε→∀ᶠ N in atTop,bills F j N ε
def Crude (μ: Family G)(F:Stem μ p) := Pasted F ∧ ∀ᶠ j in atTop, ∃ b:ℝ,∀ᶠ N in atTop,bills F j N b
structure Cloud (μ:Family G)(F:Stem μ p) : Prop where
   same : Pasted F
   silent: ∃ r:ℕ,∀ᶠ N in atTop,∀ o:Site (μ.side N p),∀ W: Config G (μ.side N p)→ℂ,Interior (Mark.Outer r o) W→ moment (μ.beta N p) (fun x=> bloom (F N) o x*W x)=0

def Wealth (μ:Family G)(F:Stem μ p) := Pasted F ∧ ∃ V:Stem μ p, Crude μ V ∧ Cloud μ (F-V)
namespace Faded
variable {F V:Stem μ p}
lemma crude (h:Faded μ F): Crude μ F:=⟨h.1,h.2.mono fun i hi=> ⟨1,hi _ one_pos⟩⟩
lemma plus (h:Faded μ F)(hp:Faded μ V)(H: Vintage.YM.Family.Makes μ): Faded μ (F+V):=by
   refine ⟨h.1.plus hp.1,(h.2.and hp.2).mono fun j ⟨hi,hh⟩ ε he=>?_⟩; filter_upwards [hi (ε/2) (half_pos he),hh _ (half_pos he),h.1.vistas j,hp.1.vistas j] with i hv hc hv' hc' hk
   exact ((Vintage.YM.Cells.seamless H i p).semi _ _ _ hv'.choose_spec hc'.choose_spec).trans ((add_le_add (hv hk) (hc hk)).trans_eq (add_halves ε))
lemma cheap (h:Faded μ F){a:ℕ→ℂ}(p:∀ᶠ i in atTop,‖a i‖ ≤ 1): Faded μ (fun i=> a i • F i):=by
   refine ⟨Pasted.smulT h.1 a,h.2.mono fun k hk ε he=>?_⟩; filter_upwards [p,hk ε he] with i hi hV hM; change Tiling.rootTest _ _ (a i • F i) ≤ ε; rw [Next.Extract.root_smul]; exact le_trans (mul_le_of_le_one_left (Tiling.root_nonneg ..) hi) (hV hM)
lemma negate (h:Faded μ F): Faded μ (-F):=by rw [← neg_one_smul ℂ F]; exact cheap h (a:=fun _=> -1) (by simp)
end Faded
namespace Crude
variable {F V:Stem μ p}
lemma plus (h:Crude μ F)(hp:Crude μ V)(H: Vintage.YM.Family.Makes μ): Crude μ (F+V):=by
   refine ⟨h.1.plus hp.1,(h.2.and hp.2).mono fun j ⟨⟨f,hf⟩,g,hg⟩=>?_⟩
   refine ⟨f+g,?_⟩; filter_upwards [hf,hg,h.1.vistas j,hp.1.vistas j] with i hv hc hv' hc' hk; exact ((Vintage.YM.Cells.seamless H i p).semi _ _ _ hv'.choose_spec hc'.choose_spec).trans (add_le_add (hv hk) (hc hk))
lemma wealth (h:Crude μ F): Wealth μ F:=⟨h.1,F,h,by rw [sub_self]; exact ⟨Pasted.nil,0,Eventually.of_forall fun n v w h=> by change moment _ (fun u=> (0:ℂ)* w u)=_; simp [moment] ⟩⟩
end Crude
-- title.P.
def garden (F:Fin n→ Stem μ p)(N:ℕ)(o:Fin n→ Site (μ.S.side N p)): ℂ:= moment (μ.beta N p) (fun V=> ∏ i,bloom (F i N) (o i) V)
def patch (F:Fin n→ Stem μ p)(N:ℕ)(o:Fin n→ Cover): ℂ:= garden F N (wrap (μ.side N p) ∘ o)
lemma dollars {β b :ℝ} (h:m ≤ N) (T:Tiling (C.side N p)) (A:Config G (C.side N p)→ℂ)(u:Site (C.side N p))
    (hw:Cells.Seam G (C.side N p) β) (hq:Cells.span C h p∣ T.side.val)(hp:Interior ((center C p h 0).chamber 0) A)(he:(center C p h 0).rootTest β A ≤ b)
    (i:T.Cell)(hx:u∈ T.margin i (3*Cells.span C h p)): ∃ F':Config G (C.side N p)→ℂ, T.copy i F'=bloom A u∧Interior (T.chamber 0) F'∧ T.rootTest β F'≤ b:=by
   obtain ⟨x,hX⟩:=T.pointed i u
   let v:= (T.omega i)⁻¹; let z:=decide (T.hand i)
   let Y:= RelayDifference.oriented A z v 0; let F (x:Site (C.side N p)):=bloom Y x
   have ha(s):F s=RelayDifference.oriented A z v s:=by
     funext U; unfold F bloom Y RelayDifference.oriented; simp only [Function.comp_apply]; rw [show translate s U=pull 1 s U from (pull_one s U).symm, pull_pull, one_mul]; simp [affine]
   have hd:RelayDifference.diag v:=RelayDifference.diag_inv rfl
   have hp' := RelayDifference.center_interior h v hd z 0 hp; have hh:= RelayDifference.offset h T β b hq (literal Y) hw (show Interior _ (F 0) from (by rw [ha]; exact hp')) (show _ ≤ b from ?_) ((T.reflected_margin x ..).2 (hX.symm ▸ hx))
   · refine ⟨F x, ?_,hh⟩; rw [ha,RelayDifference.copied,hX]; unfold bloom RelayDifference.oriented; dsimp only [v,z]; rw [mul_inv_cancel]; funext k; by_cases h:T.hand i <;> simp [RelayDifference.hand,h] <;> rw [pull_one]
   change (center C p h _).rootTest β (F 0)≤ _; rw [ha,RelayDifference.center_price h _ _ _ _ hd hp β]; exact he

lemma reckoned (H: Vintage.YM.Family.Makes μ)(F:Fin n→Stem μ p)(A:Fin n→ℝ) (k:ℕ)(hg:m≤k)(h:k≤N)(hx:(n:ℝ)*(2*(3*μ.S.a k))<μ.S.a m)
    (hh:∀ i,Interior ((tilesAt μ.S p h).chamber 0) (F i N)∧ bills (F i) k N (A i))(Y:Fin n→ Site (μ.side N p))(he:∀ i j,i≠j→ μ.S.a m < μ.S.a N*separation (Y i) (Y j)): ‖garden F N Y‖ ≤ ∏ i,A i:=by
    let T:=tilesAt μ.S p (hg.trans h); let t:= Cells.span μ.S h p; have hs:μ.S.a N*t= μ.S.a k:= μ.S.embeds_scale (μ.S.toDepth h p); have hM : μ.S.a N*T.side.val= μ.S.a m:=μ.S.embeds_scale T.units
    have hp : n*(2*(3*t)) < T.side.val:=by apply (Nat.cast_lt (α:=ℝ)).mp; apply lt_of_mul_lt_mul_left _ (μ.S.a_pos N).le; rw [hM]; rw [← hs] at hx; push_cast; linarith only [hx]
    obtain ⟨x,hx⟩:= T.fits_together Y (3*t) (by exact Nat.mul_pos (by decide) ((μ.S.toDepth h p).count.property)) hp
    let X:=T.newly x; let D i:=X.which (Y i)
    have hd i:Y i∈ X.margin (D i) (3*t):=hx i
    have hk:Injective D:=by
        intro i j hy; by_contra! ho; have hl:= X.extent (hd i).1 ((hy.symm ▸(hd j).1):Y j∈ X.chamber (D i)); have hz: separation (Y i) (Y j) ≤ T.side.val:=hl; apply (he i j ho).not_ge; rw [← hM]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hz) (μ.S.a_pos _).le
    let hS:= Vintage.YM.Cells.seamless H N p
    choose u hu hX hD using fun i=> dollars h X (F i N) (Y i) hS (Around.inherits (C:=μ) hg h) (hh i).1 ((hh i).2 h) (D i) (hd i)
    have h:= X.planted hS _ hk u hX; exact (show ‖garden F N Y‖ ≤ _ from by simpa only [hu,garden] using (h.trans (Finset.prod_le_prod (fun i _=> X.root_nonneg ..) (fun i _=> hD i))))
end YM.UVExtension.Fallow
