import YM.RG08.Town.Bauble
/-!
# Unwrapped true center path. Seam chooses upper-closed policy on coordinates,
no second root rounding. Capture integrations later needn't move outlines at seams.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Town
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series.Radial PertExtension.Series.Tested Pill Wings
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I J:Type}{u : I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e n r d τ D j k t ε i:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D}{T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
variable (X ν D')
def spanP (k i:ℕ):= X.S.a i/X.S.a k
def fareP (k i:ℕ):= min 1 (spanP X k i)
lemma spanP_pos (k i:ℕ): 0 < spanP X k i:= div_pos (X.S.a_pos _) (X.S.a_pos _)
lemma fee_posP k i : 0 < fareP X k i:= lt_min zero_lt_one (spanP_pos ..)
lemma spanP_tick k i: spanP X k (i+1)*(X.S.block i).val=spanP X k i:= by unfold spanP; rw [X.S.a_step,div_mul_eq_mul_div, div_mul_cancel₀]; positivity
lemma fee_tails (k i:ℕ): fareP X k i/(X.S.block i).val ≤ fareP X k (i+1):= by
   let a:=(↑(X.S.block i).val:ℝ); have h:1≤a:= by unfold a; exact_mod_cast (X.S.block _).property
   have hA:0<a:= by positivity
   refine le_min ((div_le_one hA).2 ((min_le_left ..).trans h)) ((div_le_iff₀ hA).2 ?_)
   unfold a; rw [spanP_tick]; exact min_le_right ..
def arcT (k i:ℕ)(x:E4) : Cover:= fun b=> ⌈x b/spanP X k i-1/2⌉
lemma inBlock (k i:ℕ)(x:E4) (b:Axis): -(1/2:ℝ) < x b / spanP X k i - (arcT X k i x b:ℤ) ∧ x b/spanP X k i - arcT X k i x b ≤ 1/2 := by
   have ht:= Int.ceil_lt_add_one (x b/spanP X k i-1/2); have hp:= Int.le_ceil (x b/spanP X k i-1/2); unfold arcT; constructor <;> linarith
def shrinkP (k i:ℕ)(x:E4): Site (X.S.block i) := wrap _ (arcT X k (i+1) x-(X.S.block i).val • arcT X k i x)
lemma arena (k i:ℕ)(x:E4): Lattice.lift (shrinkP X k i x)=arcT X k (i+1) x-(X.S.block i).val • arcT X k i x:= by
   let v:=X.S.block i; let V:=v.val; let Q:= arcT X k i x; let R:=arcT X k (i+1) x
   let a:=spanP X k i; let b:=spanP X k (i+1); have ha:0<a :=spanP_pos ..; have hb:0 < b:=spanP_pos ..; have ht:0<V:= v.property
   refine lift_eq_iff.mpr ⟨rfl,fun j=>?_⟩; simp only [Pi.sub_apply,Pi.smul_apply,nsmul_eq_mul]; obtain ⟨ρ,hρ⟩:=X.S.block_odd i
   let t:=x j/a; let u:=x j/b
   have hx : (V:ℝ)*t=u:= by unfold u t; rw [show a=b*V from (spanP_tick ..).symm]; field_simp
   have hy : -(V:ℝ)-1 < 2*(↑(R j)-(V:ℝ)*(Q j)) ∧ 2*(↑(R j)-(V:ℝ)*(Q j)) < V+1 := by
     obtain ⟨hG,hZ⟩ : -(1/2:ℝ)< t-(Q j:ℝ) ∧ t-Q j≤1/2:=inBlock ..; obtain ⟨hA,hB⟩: -(1/2:ℝ)< u-(R j:ℝ) ∧ u-(R j)≤1/2:=inBlock ..
     constructor <;> nlinarith only [mul_lt_mul_of_pos_left hG (show 0<(V:ℝ) by positivity),mul_le_mul_of_nonneg_left hZ (show 0≤(V:ℝ) by positivity),hx,hA,hB]
   have h': -(V:ℤ)-1 < 2*(R j-V*Q j) ∧ 2*(R j-V*Q j)< V+1:= by exact_mod_cast hy
   have hV:V=2*ρ+1:= hρ; change -(V:ℤ)<2*((R j)-V*Q j) ∧ 2*((R j)-V*Q j)≤V; omega
lemma stairsP (w:J→ShoreP u)(k:J→ℕ): Arbor X w (fun i=> fareP X (k i.a) i.i):=⟨fun i=>(fee_posP ..).le,fun i=>min_le_left ..,fun i=>fee_tails ..⟩
def dustP (N y ε i:ℕ)(U:Tale G): Tale G:= if h:i<y then inscribed ε (dance X ν D' N i) (0: Site (X.S.block i)) (dustP N y ε (i+1) U) else U
termination_by y-i
@[simp] lemma dust_top (N y ε:ℕ)(U:Tale G): dustP X ν D' N y ε y U=U:= by rw [dustP, dif_neg (lt_irrefl y)] -- declaration uses ν order?
lemma dust_step (N i y ε:ℕ)(U:Tale G)(h:i<y): dustP X ν D' N y ε i U=inscribed ε (dance X ν D' N i) 0 (dustP X ν D' N y ε (i+1) U):= by rw [dustP,dif_pos h]
variable {X ν D'}
lemma wall_path (V:Wall w 0→Tale G)(h:∀ i:Wall w 0,(w i.a).next.i=i.i → Stone ε (V i))(Z:∀ i:Wall w 1,StripU G (X.S.block i.i)) (ρ:∀ i:Wall w 1,Site (X.S.block i.i))(hv:∀ i,Fair (Z i))(he : ∀ i:Wall w 1,V i.low=inscribed ε (Z i) (ρ i) (V i.roof))(i: Wall w 0): Stone ε (V i):= by
   generalize hN:(w i.a).next.i-i.i=n; induction n using Nat.strong_induction_on generalizing i with
   | h n ih=>
     by_cases hp: i.i < (w i.a).next.i
     · let p: Wall w 1:=⟨i.a,i.i,i.first,hp⟩; have hh: (w p.roof.a).next.i - p.roof.i < n:= by change _ -(i.i+1)<n; unfold Wall.roof p; dsimp only; omega
       rw [show V i= _ from he p]; exact inscribe_law _ (hv _) (ih _ hh p.roof rfl)
     have he:=i.last; exact h i (by omega)
variable (X ν D')
def dusts (w:J→ ShoreP u)(F:J→ℕ)(V:J→Tale G)(ε:ℕ)(i:Wall w 0):= dustP X ν D' (F i.a) (w i.a).next.i ε i.i (V i.a)
def lampP (X:Chain)(k:J→ℕ)(x:J→E4) (V:Wall w 0→Tale G) (i:Wall w 0):= season (-arcT X (k i.a) i.i (x i.a)) (V i)
variable {X ν D'}
section supply
variable {U V:J→Tale G}(he:Tights T S ν D' u)
lemma taste_dust (U:J→Tale G)(p:J→ℕ)(hp:∀ i,Stone ε (U i)) (Z: ∀ i:Wall w 1,Fair (dance X ν D' (p i.a) i.i)) : ∀ i, Stone ε (dusts X ν D' w p U ε i) := by
   let d:=dusts X ν D' w p U ε
   have he h (hk: (w h.a).next.i=h.i): Stone ε (d (h: Wall w 0)) := by unfold d dusts; rw [hk,dust_top]; exact hp _ -- h binder inferred?
   exact wall_path (X:=X) d he (fun i=> dance X ν D' (p i.a) i.i) (fun _=>0) Z fun i=> dust_step _ _ _ _ _ _ _ _ i.last
lemma lamp_d (K:Wall w 1→ Wings u 1)(N:J→ℕ)(hp:∀ i:Wall w 1,(K i).i=i.i)(t:Wall w 1)(hv:Fair (dance X ν D' (N t.a) t.i)) (h:Stone ε (dustP X ν D' (N t.a) (w t.a).next.i ε (t.i+1) (V t.a)))(k:J→ℕ)(x:J→E4):
    let F:= lampP X k x (dusts X ν D' w N V ε); let s:= shrinkP X (k t.a) t.i (x t.a)
    F t.low=inscribed ε (dance X ν D' (N t.a) t.i) s (F t.roof):= by
   intro F s; let Q := arcT X (k t.a) t.i (x t.a)
   change season (-Q) (dustP X ν D' (N t.a) (w t.a).next.i ε t.i (V t.a))=inscribed ε _ _ (season (-arcT X (k t.a) (t.i+1) (x t.a)) _); rw [dust_step _ _ _ _ _ _ _ _ t.last]; refine Eq.symm (order_moves (p:=0) (q:=s) h hv (Y:=-Q) ?_); unfold s; rw [arena]; have hx(p:Side): Lattice.lift (0:Site p)=0:= by ext; simp [Lattice.lift]; -- invert
   simp only [hx,add_zero,Q,smul_neg]; abel
include he
lemma lamp_l (hp:∀ i,Stone ε (U i))(k:J→ℕ)(x:J→E4): Tie (lampP X k x (dusts X ν D' w (fun i=>(w i).next.N) U ε)) X ν D' ε wallL (fun i=>shrinkP X (k i.a) i.i (x i.a)) := by
   let N i:=(w i).next.N; have hP :=taste_dust (D':=D') (X:=X) U N hp (fun i:Wall w 1=> he.fair (wallL i))
   exact ⟨fun i=>rfl,fun i=>(hP i).transport _,fun i=> lamp_d wallL N (fun i=>rfl) i (he.fair (wallL i)) (hP i.roof) k x⟩
lemma lamp_r (hp:∀ i,Stone ε (U i))(k:J→ℕ)(x:J→E4): Tie (lampP X k x (dusts X ν D' w (fun i=>(w i).next.M) U ε)) X ν D' ε wallR (fun i=>shrinkP X (k i.a) i.i (x i.a)) := by
   let N i:=(w i).next.M; have hP:= taste_dust (D':=D') (X:=X) U N hp (fun i:Wall w 1=> he.fair (wallR i)); exact ⟨fun i=>rfl,fun i=>(hP i).transport _,fun i=>lamp_d wallR N (fun i=>rfl) i (he.fair (wallR i)) (hP i.roof) k x⟩
local notation "Ⓨ" => wallY X
variable {p q:J→ℝ}{b:J→ℕ}{x:J→E4}{δ:Wall w 0→ℝ}
omit he in
def saleP (b:J→ℕ)(x:J→E4)(U:J→Tale G)(j:J):= season (-arcT X (b j) (w j).next.i (x j)) (U j)
omit he in
def scaleP (X:Chain)(b:J→ℕ)(i:Wall w n):= fareP X (b i.a) i.i
omit he in
lemma flat_l (p:J→ℕ)(i:J): lampP X b x (dusts X ν D' w p V ε) (Wall.tip w i)=saleP (w:=w) (X:=X) b x V i:= by unfold lampP dusts Wall.tip saleP; dsimp only; rw [dust_top]
set_option linter.unusedVariables false in
/-- Bounds in evaluation distance norm `◇` (up to fixed-power equivalence), native distance to every field charged even when many independent endpoints, $\eta$ cost not wrapped. Only the stated marked-read tilt, no common-volume constants. -/
theorem rowing (hp:Pines A u)(hX:Arbor X w δ)(hx:∀ i:Wall w 1, tiltP X i ≤ q i.a)(hr:∀ i,Stone ε (U i))(hu:∀ i,Stone ε (V i))(hy:ε≤τ)(hz:0≤p)(hq:0≤q)
   (he':∀ i≤E,∀ j, Drum k (fun t=>Ⓨ (Wall.tip w t)) q p (fun t=>saleP (w:=w) (X:=X) b x U t i j) (fun t=>saleP (w:=w) (X:=X) b x V t i j) (fun t=>δ (Wall.tip w t))) :
    let S:= lampP X b x (dusts X ν D' w (fun i=>(w i).next.N) U ε); let S':=lampP X b x (dusts X ν D' w (fun i=>(w i).next.M) V ε)
    ∀ i≤E,∀ j, Drum k Ⓨ (badge q) (badge p) (fun t=> S t i j) (fun t=> S' t i j) δ ∧ (j≠0 → Drum k Ⓨ (badge q) (strideP X w p) (fun t=> S t i j) (fun t=> S' t i j) δ) := by
   intro S Q i hi j
   have hk:= lamp_l (w:=w) he hr b x; have hh:= lamp_r (w:=w) he hu b x; have hv(i)(he:i≤E)(j): Drum k (fun t=>Ⓨ (Wall.tip w t)) q p (fun t=> S (Wall.tip w t) i j) (fun t=> Q (Wall.tip w t) i j) (fun t=>δ (Wall.tip w t)):= by unfold S Q; simp_rw [flat_l]; exact he' i he j
   exact ⟨wines hp he hy hk hh hX hx hz hq hi hv,fun h=>visits hp he hy hk hh hX hx hz hq hi h (fun i he j _=>hv i he j)⟩
end supply
end YM.RG08.Town
