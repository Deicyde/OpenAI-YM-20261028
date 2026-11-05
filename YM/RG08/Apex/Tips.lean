import YM.RG08.Apex.Rest
/-! # Parallel schedules and fixed wings, coherence. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums UVExtension.Free
open scoped BigOperators Topology Real Classical
variable {I J : Type} {u : I→Windows} {r e : ℕ}
lemma SafeRow.mold {α β:I→Type}{S:∀i,Row (α i) (β i)} {y δ w} (h : SafeRow y δ S w)(f : J→I) : SafeRow (fun i=> y (f i)) (fun i=>δ (f i)) (fun i=>S (f i)) (fun i=> w (f i)) :=
  ⟨_,h.choose_spec.1.transfer f,fun b=>h.choose_spec.2 (f b)⟩
lemma Both.mold {α:I→Type}{P Q:∀i,Shale (α i) r}{y δ w}(h : Both y δ P Q w)(f:J→I) : Both (fun i=>y (f i)) (fun i=>δ (f i)) (fun i=>P (f i)) (fun i=>Q (f i)) (fun i=>w (f i)) := ⟨h.fresh.mold f,h.again.mold f,h.moves.mold f⟩
lemma RowBoth.mold {α β:I→Type}{P Q:∀i,Row (α i) (β i)}{y δ w}(h : RowBoth y δ P Q w)(f:J→I) : RowBoth (fun i=>y (f i)) (fun i=>δ (f i)) (fun i=>P (f i)) (fun i=>Q (f i)) (fun i=>w (f i)) := ⟨h.fresh.mold f,h.again.mold f,h.moves.mold f⟩
lemma Both.mended {α : Type} {δ : ℕ→ℝ}{V:ℕ→Shale α r}{F:Shale α r}{y B : ℝ}(h : Both (fun _=>y) δ V (fun _=> F) (fun _=>B))(hp : 0 ≤ δ)(hx: Tendsto δ atTop (𝓝 0))(hv : 0<B) : Mending V F := by
  obtain ⟨A,hA,H⟩:=h.again; obtain ⟨C,⟨K,q,hp',hh⟩,H'⟩:=h.moves
  exact ⟨⟨_,_,hv,H 0⟩,_,fun i=> K*y^q*δ i,hv,by simpa using hx.const_mul (K*y^q),fun i=> glow_less (H' i) le_rfl (mul_le_mul_of_nonneg_right (hh i).2 (hp i))⟩
lemma Mending.played {α : Type}{F:ℕ→Shale α r}{V : Shale α r}(h:Mending F V) : Tendsto F atTop (𝓝 V) := by
  obtain ⟨B,C,hp,hc,H⟩:=h.2; apply tendsto_pi_nhds.mpr; intro i; apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _=> norm_nonneg _) (fun j=>?_ ) hc
  exact (le_mul_of_one_le_left (norm_nonneg _) (ling_one hp.le i)).trans (budget_single (H j) _)
lemma Mending.sing {α:Type}[Fintype α]{F:ℕ→Shale α r}{V:Shale α r}(h:Mending F V)(hp:∀i,Tunable (F i)) : Tunable V := by
  have hv (i) : F i-V=score (F i)-V := by rw [(hp i).score_eq]
  have he : Vanished (fun i=>score (F i)-score V) := by
    simp_rw [← score_sub (hp _).1 h.1.summable]; exact h.2.scored
  have hh : Glows (score V) := by
    obtain ⟨w,A,hv,H⟩:= h.1
    let v:=w/(r+1:ℕ); have hp:0<v:=div_pos hv (by positivity)
    exact ⟨_,_,hp,score_price (glow_less H (mul_div_cancel₀ w (by positivity)|>.le) le_rfl) hp.le⟩
  have hh' : Mending F (score V) := ⟨hh,by simpa only [(hp _).score_eq] using he⟩
  rw [tendsto_nhds_unique h.played hh'.played]; exact score_tunable h.1.summable

namespace Summit
open Chain Wings

def quartz (X : Chain) (G : Gauge)(i : ℕ) := apex (fun N=> column G X N i)
def amber (X : Chain) (G : Gauge)(i : ℕ) := apex (fun N=>predict G X N i)
def slate (X : Chain) (G : Gauge)(i : ℕ) := apex (fun N=> curve G X N i)
def quarry (X : Chain) (i : ℕ) := apex (fun N=>X.K₀ N i)
def statue {G : Gauge}(X : Chain)(ν : G.ColorIndex)(D : ChartRatio G)(i : ℕ) : Air G := fun e r=> apex (fun N=> X.album ν D N i e r)
def granite {G : Gauge}(X : Chain)(ν : G.ColorIndex)(D : ChartRatio G)(i : ℕ) : Air G := fun e r=> apex (fun N=> X.compassRaw ν D N i e r)
variable {X : Chain}{G : Gauge}{K : KPrices X.kernel}{g:KGate K}{P : Lending G X.kernel}{E : ℕ}{S : Prism G X.kernel g P E}{ν:G.ColorIndex}{D:ChartRatio G}

lemma smooth (h : Circuit S ν D u)(hp : X.Wake G) : RowBoth (menu X) (chop X (1/4))
    (fun i:Wings u 1=> curve G X i.N i.i) (fun i=> slate X G i.i) (fun i=>ticketW P (X.J i.i)) :=
   highRate (F:=curve G X) (fun i=> ticket_pos ..) (gear_both h hp).1
lemma polishes (h : Circuit S ν D u)(hp : X.Wake G) : RowBoth (menu X) (chop X (1/4))
    (fun i:Wings u 1=>predict G X i.N i.i) (fun i=> amber X G i.i) (fun i=>ticketW P (X.J i.i)) :=
   highRate (F:=predict G X) (fun i=>ticket_pos ..) (gear_both h hp).2
lemma kernel_pay (h : Circuit S ν D u) : RowBoth (menu X) (chop X (1/4))
    (fun i:Wings u 0=> X.K₀ i.N i.i) (fun i=> quarry X i.i) (fun i=>g.w (X.J i.i)) := by
  apply highRate (F:=X.K₀) (fun _=>g.pos _)
  have hh (A : Wings u 0→ℕ) : SafeRow (menu X) 1 (fun i=> X.K₀ (A i) i.i) (fun i=>g.w (X.J i.i)) := ⟨_,h.hessian.transfer toLaunch,fun i=> strip_mono (k_strip X K (A i) i.i) (g.small _) (by simp only [Pi.one_apply,mul_one,le_refl])⟩
  exact ⟨hh N, hh M, mail h⟩
lemma patched (h : Circuit S ν D u) : Both (menu X) (chop X (1/4)) (fun i:Wings u 0=> orbit (G:=G) X i) (fun i=> quartz X G i.i) (fun i=> Tier S i.i) := Both.landed (F:=column G X) (q_right h) (fun _=> (S.positive _).le)
lemma statues (h : Circuit S ν D u)(hp : X.Wake G)(hv : LocalRatio D)(hs : G.Simple)(he:e ≤ E)(r) : Both (menu X) (chop X (1/4)) (fun i:Wings u 0=> moon X ν D i e r) (fun i=> statue X ν D i.i e r) (fun i=>Tier S i.i) := Both.landed (F:=fun n i=> X.album ν D n i e r) (skater h hs hp hv he r).top (fun _=> (S.positive _).le)
lemma graces (h : Circuit S ν D u)(hp : X.Wake G)(hv : LocalRatio D)(hs : G.Simple)(he:e ≤ E)(r): Both (menu X) (chop X (1/4)) (fun i:Wings u 1=> lunar X ν D i e r) (fun i=> granite X ν D i.i e r) (fun i=>Tier S i.i) := Both.landed (F:=fun n i=> X.compassRaw ν D n i e r) (skater h hs hp hv he r).pre (fun _=> (S.positive _).le)
end Summit
end YM.RG08
