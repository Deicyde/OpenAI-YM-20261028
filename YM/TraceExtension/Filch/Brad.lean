import YM.TraceExtension.Filch.Manor
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Filch
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295.Cases
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}
variable {X : Type}[NormedAddCommGroup X][NormedSpace ℝ X]{k:ℕ}
variable {I:Type} [Fintype I]
def stone (A:I→ℕ)(r:ℕ): Rays I→L[ℝ] Rays I:= ContinuousLinearMap.pi fun i=> if A i ≤ r then ContinuousLinearMap.proj i else 0
lemma stone_at(A:I→ℕ)(r:ℕ)(x:Rays I)(i:I):stone A r x i=if A i≤r then x i else 0:=by unfold stone; rw [ContinuousLinearMap.pi_apply]; split <;> rfl
lemma enthral {Y V:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup V][NormedSpace ℝ V](F H:X→ Y)(G:Y→V)(v:Y)(hF: F 0=v)(hH:H 0=v)(h:braid F H 0 k) (ha:ContDiffAt ℝ ω G v)(hp:ContDiffAt ℝ ω F 0)(hy:ContDiffAt ℝ ω H 0) : braid (G ∘ F) (G ∘ H) 0 k:=by
    intro i hi; ext1 z; rw [compReads (hF.symm ▸ ha) hp (by simp),compReads (hH.symm ▸ ha) hy (by simp)]; apply sum_congr rfl; intro b _; unfold caseRead
    simp_rw [hF,hH,h _ ((b.partSize_le _).trans hi)]
lemma stone_r(o:Site n)(r:ℕ)(W:Coats G n)(v:Acr G n): stone (landW o) r (loyG W v)=loyG W (stone (landW o) r v):=by
    let K:= armor W; let P:= stone (landW (G:=G) o) r; let Z:=loyG W
    have hp(e:Edge (Site n))(u:Acr G n): edgeColor (aleft G n (P u)) e = if separation o e.1≤r then edgeColor (aleft G n u) e else 0:=by ext i; split <;> rename_i he <;> exact (stone_at (landW o) r u (.inl (e.1,coord e.2,i))).trans (by simp [landW,he] <;> rfl)
    have hv(e:Edge (Site n))(u:Acr G n): edgeColor (aright G n (P u)) e = if separation o e.1≤r then edgeColor (aright G n u) e else 0:=by ext i; split <;> rename_i he <;> exact (stone_at (landW o) r u (.inr (e.1,coord e.2,i))).trans (by simp [landW,he] <;> rfl)
    apply (bite G n).injective; rw [loyX]; refine Prod.ext (edgeColor.injective (funext (fun e=> ?_))) (edgeColor.injective (funext (fun e=>?_)))
    · change edgeColor (aleft G n (P (Z v))) _= edgeColor (armor W (aleft G n (P v))) _; rw [hp,show aleft G n (Z v)=_ from congr_arg Prod.fst (loyX W v),armor_at,armor_at,hp]; split <;> simp_all
    change edgeColor (aright G n (P (Z v))) _=edgeColor (armor W (aright G n (P v))) _; rw [hv,show aright G n (Z v)=_ from congr_arg Prod.snd (loyX W v), armor_at,armor_at,hv]; split <;> simp_all

def cloud (F:Acr G n→ℝ)(o:Site n)(r:ℕ)(U:Config G n)(v:Link G n):= choral 4 F (stone (landW o) r (patio o 4 U v))
lemma cloudful (F:Acr G n→ℝ)(o:Site n)(r:ℕ)(U:X→ Config G n)(v:X→ Link G n)(x:X)(h:Army U x)(hp:ContDiffAt ℝ ω v x):ContDiffAt ℝ ω (fun y=>cloud F o r (U y) (v y)) x:= (rhythm F _).contDiffAt.comp _ ((stone (landW (G:=G) o) r).contDiff.contDiffAt.comp _ (patioW o _ U v x h hp))
lemma cloud_r {F:Acr G n→ℝ}(he:ContDiffAt ℝ ω F 0)(ht:∀ u:G.El,F=ᶠ[𝓝 0] F ∘ loyG (fun _=>u))(o:Site n)(r:ℕ)(U:Config G n)(W:Coats G n)(v:Link G n): cloud F o r (Lattice.gauge W U) (armor W v)=cloud F o r U v:=by
    unfold cloud; rw [loyY,stone_r]; exact (intoned _ F F (ht (W o)) _ he _).symm
lemma cloud_local (F:Acr G n→ℝ)(o:Site n)(r:ℕ)(v:Link G n): LocalOn (feed o (r+1)) (fun U=> cloud F o r U v):=by
    intro U V H; apply congr_arg (choral 4 F); ext1 i; rw [stone_at,stone_at]; split <;> rename_i h; swap; rfl
    cases i with
    | inl j=> rcases j with ⟨y,p,l⟩; obtain ⟨b,rfl⟩:= axisEquiv.surjective p; change patio o 4 U v (.inl (y,coord b,l))= patio o 4 V v (.inl (y,coord b,l)); rw [patioX,patioX]; exact congr_arg (fun u=> nimbus G 4 u l) (eaten o y b h U V H)
    | inr j=>
       rcases j with ⟨y,p,l⟩; obtain ⟨b,rfl⟩:= axisEquiv.surjective p; change patio o 4 U v (.inr (y,coord b,l))= patio o 4 V v (.inr (y,coord b,l)); rw[patioY,patioY]; exact congr_arg (fun u=> G.adjoint u (edgeColor v (y,b)) l) (grazes o y (r:=r+1) (le_trans h (Nat.le_succ r)) U V H)
lemma cloudV (F:Acr G n→ℝ)(o:Site n)(r:ℕ)(v w:Link G n)(U:Config G n)(h:∀ e:Edge (Site n),separation o e.1≤r→ edgeColor v e=edgeColor w e): cloud F o r U v=cloud F o r U w:=by
    apply congr_arg (choral 4 F); ext1 i; rw[stone_at,stone_at]; split <;> rename_i ht; swap; rfl
    cases i with
    | inl j=> rw[patio,patioA o,patio,patioA o]
    | inr j=> rcases j with ⟨y,p,l⟩; obtain ⟨b,rfl⟩:=axisEquiv.surjective p; change patio o 4 U v (.inr (y,coord b,l))=patio o 4 U w (.inr (y,coord b,l)); rw[patioY,patioY,h (y,b) ht]
end YM.Trace.Filch
