module
public import RequestProject.Oxide.Metatheory.Progress.Helpers

/-!
# Progress, part 6: the main induction

Progress is proved by induction on the typing derivation, generalized to stack
typings that *refine* the stack typing satisfied by the stack (since `T-Drop`
kills places of the stack typing without changing the stack).
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-- Progress for argument lists: either all arguments are values (and there are
`k` of them), or the first non-value argument aborts or steps. -/
def ArgsProg (G : GlobalEnv) (σ : Stack) {n : Nat} (es : Terms n) (k : Nat) : Prop :=
  (∃ vs, es = Terms.ofVals vs .nil ∧ vs.length = k) ∨
    ∃ vs e rest, es = Terms.ofVals vs (.cons e rest) ∧
      ((∃ s, e = .abort s) ∨ ∃ σ' e', Step G σ e σ' e')

/-- The statement proved by induction on typing derivations. -/
def ProgMotive (G : GlobalEnv) : TyJ → Prop
  | .expr _ _ Γ e _ _ => ∀ Γ₀ σ, Refines Γ Γ₀ → StoreValid G Γ₀ σ →
      e.IsFinal ∨ ∃ σ' e', Step G σ e σ' e'
  | .args _ _ Γ es τs _ => ∀ Γ₀ σ, Refines Γ Γ₀ → StoreValid G Γ₀ σ → ArgsProg G σ es τs.length
  | .argsRw _ _ Γ es τs _ => ∀ Γ₀ σ, Refines Γ Γ₀ → StoreValid G Γ₀ σ →
      ArgsProg G σ es τs.length
  | .val .. => True
  | .vals .. => True

theorem PlaceExpr.toAbs_ops {n : Nat} {Γ : StackTy} {p : PlaceExpr n} {pa : APlaceExpr}
    (h : p.toAbs Γ = some pa) : pa.ops = p.ops := by
  simp only [PlaceExpr.toAbs, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

theorem HasTypeV.u32_inv {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {v : Value}
    (h : HasTypeV G Δ Θ Γ v Ty.u32) : ∃ k, v = Value.num k :=
  (canonical_forms h).2.1 rfl

theorem HasTypeV.bool_inv {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {v : Value}
    (h : HasTypeV G Δ Θ Γ v Ty.bool) : ∃ b, v = .prim (.bool b) :=
  (canonical_forms h).1 rfl

theorem HasTypeV.fn_inv {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {f : String} {nφ nϱ nα : Nat}
    {ps : List Ty} {τf : Ty} {Φ : FrameExpr} {bs : List (Nat × Nat)}
    (h : HasTypeV G Δ Θ Γ (.fn f) (.fn nφ nϱ nα ps τf Φ bs)) :
    ∃ d, G.lookup f = some d ∧ d.params = ps := by
  cases h with
  | vFn _ _ _ _ d hd => exact ⟨d, hd, rfl⟩

theorem HasTypeV.not_slice_of_SI' {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {w : Value}
    {τ : Ty} (h : HasTypeV G Δ Θ Γ w τ) (hsi : τ.SI) : ∀ ws, w ≠ .slice ws := by
  rintro ws rfl
  exact h.not_slice_of_SI hsi

/-- Sequences and arrays of indexed values: reading the base of an indexed
place gives an array or a slice. -/
theorem HasTypeV.seq_inv {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {w : Value} {τ τ' : Ty}
    (h : HasTypeV G Δ Θ Γ w τ) (hτ : (∃ k, τ = .array τ' k) ∨ τ = .slice τ') :
    ∃ vs, w = .array vs ∨ w = .slice vs := by
  rcases hτ with ⟨k, rfl⟩ | rfl
  · obtain ⟨vs, rfl, -⟩ := h.array_inv; exact ⟨vs, .inl rfl⟩
  · obtain ⟨vs, rfl, -⟩ := h.slice_inv; exact ⟨vs, .inr rfl⟩

theorem progress_aux {J : TyJ} (h : Typing G J) : ProgMotive G J := by
  induction h with
  | val => intro Γ₀ σ hR hσ; exact .inl (.inl ⟨_, rfl⟩)
  | move Δ Θ Γ Γ' p π τ hp hsafe hty hsi hnc hΓ' =>
    intro Γ₀ σ hR hσ
    obtain ⟨w, τ₀, Θ', k, hE, hr, hτ, hw⟩ := place_eval_path hR hσ hp hty
    have e := hτ.dead_left_SI hsi
    subst e
    obtain ⟨σ', hσ'⟩ := Stack.write_some hr (.inl (hw.not_slice_of_SI' hsi)) .dead
    have hops := PlaceExpr.toAbs_ops hp
    refine .inr ⟨_, _, Step.move σ σ' p _ w ?_ hE hr hσ'⟩
    rw [← hops]
    simp [APlace.toExpr]
  | copy Δ Θ Γ p pa L τ ρs hp hsafe htc hsi hc =>
    intro Γ₀ σ hR hσ
    obtain ⟨R, w, Θ', k, hE, hr, -⟩ := place_eval hR hσ hp htc
    exact .inr ⟨_, _, Step.copy σ p R w hE hr⟩
  | borrow Δ Θ Γ r ω p pa L τ ρs hp hr hnic hsafe htc hxi =>
    intro Γ₀ σ hR hσ
    obtain ⟨R, w, Θ', k, hE, hr, -⟩ := place_eval hR hσ hp htc
    exact .inr ⟨_, _, Step.borrow σ (.conc r) ω p R w hE hr⟩
  | borrowIdx Δ Θ Γ Γ₁ r ω p e pa L τ τ' ρs he hp hr hnic hsafe htc hτ hsi ih =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hR₁, hv⟩ := HasType.val_inv' he
      obtain ⟨i, rfl⟩ := hv.u32_inv
      obtain ⟨R, w, Θ', k, hE, hrd, hw⟩ := place_eval (hR₁.trans hR) hσ hp htc
      obtain ⟨vs, hvs⟩ := hw.seq_inv hτ
      have hrd' : σ.read R = some (.array vs) ∨ σ.read R = some (.slice vs) := by
        rcases hvs with rfl | rfl
        · exact .inl hrd
        · exact .inr hrd
      by_cases hi : i < vs.length
      · exact .inr ⟨_, _, Step.borrowIdx σ (.conc r) ω p R vs i hE hrd' hi⟩
      · exact .inr ⟨_, _, Step.borrowIdxOOB σ (.conc r) ω p R vs i hE hrd' (by omega)⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.borrowIdx (.conc r) ω p) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.borrowIdx (.conc r) ω p) σ σ' e e' hs⟩
  | borrowSlice Δ Θ Γ Γ₁ Γ₂ r ω p e₁ e₂ pa L τ τ' ρs he₁ he₂ hp hr hnic hsafe htc hτ hsi
      ih₁ ih₂ =>
    intro Γ₀ σ hR hσ
    rcases ih₁ Γ₀ σ hR hσ with (⟨v₁, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hR₁, hv₁⟩ := HasType.val_inv' he₁
      obtain ⟨i, rfl⟩ := hv₁.u32_inv
      rcases ih₂ Γ₀ σ (hR₁.trans hR) hσ with (⟨v₂, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
      · obtain ⟨hR₂, hv₂⟩ := HasType.val_inv' he₂
        obtain ⟨j, rfl⟩ := hv₂.u32_inv
        obtain ⟨R, w, Θ', k, hE, hrd, hw⟩ := place_eval ((hR₂.trans hR₁).trans hR) hσ hp htc
        obtain ⟨vs, hvs⟩ := hw.seq_inv hτ
        have hrd' : σ.read R = some (.array vs) ∨ σ.read R = some (.slice vs) := by
          rcases hvs with rfl | rfl
          · exact .inl hrd
          · exact .inr hrd
        by_cases hij : i ≤ j ∧ j ≤ vs.length
        · exact .inr ⟨_, _, Step.borrowSlice σ (.conc r) ω p R vs i j hE hrd' hij.1 hij.2⟩
        · exact .inr ⟨_, _, Step.borrowSliceOOB σ (.conc r) ω p R vs i j hE hrd' hij⟩
      · exact .inr ⟨_, _, Step.ctxAbort (.borrowSlice₂ (.conc r) ω p (Value.num i)) σ s⟩
      · exact .inr ⟨_, _, Step.ctx (.borrowSlice₂ (.conc r) ω p (Value.num i)) σ σ' e₂ e' hs⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.borrowSlice₁ (.conc r) ω p e₂) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.borrowSlice₁ (.conc r) ω p e₂) σ σ' e₁ e' hs⟩
  | index Δ Θ Γ Γ' p e pa L τ τ' ρs he hp hsafe htc hτ hsi hc ih =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hR₁, hv⟩ := HasType.val_inv' he
      obtain ⟨i, rfl⟩ := hv.u32_inv
      obtain ⟨R, w, Θ', k, hE, hrd, hw⟩ := place_eval (hR₁.trans hR) hσ hp htc
      obtain ⟨vs, hvs⟩ := hw.seq_inv hτ
      have hrd' : σ.read R = some (.array vs) ∨ σ.read R = some (.slice vs) := by
        rcases hvs with rfl | rfl
        · exact .inl hrd
        · exact .inr hrd
      by_cases hi : i < vs.length
      · exact .inr ⟨_, _, Step.index σ p R vs i vs[i] hE hrd' (List.getElem?_eq_getElem hi)⟩
      · exact .inr ⟨_, _, Step.indexOOB σ p R vs i hE hrd' (by omega)⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.index p) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.index p) σ σ' e e' hs⟩
  | seq Δ Θ Γ Γ₁ Γ₂ e₁ e₂ τ₁ τ₂ h₁ hsi₁ h₂ hsi₂ ih₁ ih₂ =>
    intro Γ₀ σ hR hσ
    rcases ih₁ Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · exact .inr ⟨_, _, Step.seq σ v e₂⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.seq e₂) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.seq e₂) σ σ' e₁ e' hs⟩
  | ite Δ Θ Γ Γ₁ Γ₂ Γ₃ Γ₂' Γ₃' Γ' e₁ e₂ e₃ τ τ₂ τ₃ h₁ h₂ h₃ hτ hsi hsi₂ hsi₃ hr₂ hr₃ hu
      ih₁ ih₂ ih₃ =>
    intro Γ₀ σ hR hσ
    rcases ih₁ Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨-, hv⟩ := HasType.val_inv' h₁
      obtain ⟨b, rfl⟩ := hv.bool_inv
      cases b
      · exact .inr ⟨_, _, Step.iteFalse σ e₂ e₃⟩
      · exact .inr ⟨_, _, Step.iteTrue σ e₂ e₃⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.ite e₂ e₃) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.ite e₂ e₃) σ σ' e₁ e' hs⟩
  | letE Δ Θ Γ Γ₁ Γ₁' Φ Γ₂ τa τ₁ τ₂ τd e₁ e₂ h₁ hsi₁ hsia hr hnrb h₂ hsi₂ hsd ih₁ ih₂ =>
    intro Γ₀ σ hR hσ
    rcases ih₁ Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · exact .inr ⟨_, _, Step.letE σ τa v e₂⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.letE τa e₂) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.letE τa e₂) σ σ' e₁ e' hs⟩
  | letrgn Δ Θ Γ Φ Γ' L e τ h hsi hfresh ih =>
    intro Γ₀ σ hR hσ
    exact .inr ⟨_, _, Step.letrgn σ e⟩
  | assignDeref Δ Θ Γ Γ₁ Γ' p e pa L τn τo ρs he hsin hsio hp htc hr hsafe ih =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hR₁, -⟩ := HasType.val_inv' he
      obtain ⟨R, w, Θ', k, hE, hrd, hw⟩ := place_eval (hR₁.trans hR) hσ hp htc
      obtain ⟨σ', hσ'⟩ := Stack.write_some hrd (.inl (hw.not_slice_of_SI' hsio)) v
      exact .inr ⟨_, _, Step.assign σ σ' p R v hE hσ'⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.assign p) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.assign p) σ σ' e e' hs⟩
  | assign Δ Θ Γ Γ₁ Γ' Γ'' p e π τ τx he hsi hp hx hsx huniq hr hsafe hΓ'' ih =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hR₁, -⟩ := HasType.val_inv' he
      obtain ⟨w, τ₀, Θ', k, hE, hrd, -, -⟩ := place_eval_path (hR₁.trans hR) hσ hp hx
      obtain ⟨σ', hσ'⟩ := Stack.write_some hrd (.inr (by simp)) v
      exact .inr ⟨_, _, Step.assign σ σ' p _ v hE hσ'⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.assign p) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.assign p) σ σ' e e' hs⟩
  | whileE Δ Θ Γ Γ₁ Γ₂ e₁ e₂ h₁ h₂ h₁' h₂' =>
    intro Γ₀ σ hR hσ
    exact .inr ⟨_, _, Step.whileE σ e₁ e₂⟩
  | forArray Δ Θ Γ Γ₁ e₁ e₂ τ τd k h₁ hsi hnrb h₂ hsd ih₁ ih₂ =>
    intro Γ₀ σ hR hσ
    rcases ih₁ Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨-, hv⟩ := HasType.val_inv' h₁
      obtain ⟨vs, rfl, -⟩ := hv.array_inv
      cases vs with
      | nil => exact .inr ⟨_, _, Step.forEmptyArray σ e₂⟩
      | cons v vs => exact .inr ⟨_, _, Step.forArray σ v vs e₂⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.forE e₂) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.forE e₂) σ σ' e₁ e' hs⟩
  | forSlice Δ Θ Γ Γ₁ e₁ e₂ ρ ω τ τx h₁ hsi hnrb h₂ hsx ih₁ ih₂ =>
    intro Γ₀ σ hR hσ
    rcases ih₁ Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hR₁, hv⟩ := HasType.val_inv' h₁
      obtain ⟨R, rfl, hRt⟩ := hv.ref_inv
      obtain ⟨R', i, j, rfl, hij, hbase⟩ := (hRt.refine (hR₁.trans hR)).slice_inv
      obtain ⟨vs, hvs⟩ := RefTy.read_seq hσ hbase
      rcases Nat.lt_or_eq_of_le hij with hij | rfl
      · exact .inr ⟨_, _, Step.forSlice σ R' i j vs e₂ hvs hij⟩
      · exact .inr ⟨_, _, Step.forEmptySlice σ R' i e₂⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.forE e₂) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.forE e₂) σ σ' e₁ e' hs⟩
  | closure Δ Θ Γ k ps ret body m ρ body' caps rs Φc Φ' Γ' hk hsi hsir hbody hmono hocc
      hcapLen hcaps hrsNodup hrs hrsBound hΦc hparams hb ih =>
    intro Γ₀ σ hR hσ
    have hex : ∀ j : Fin m, ∃ v, σ.topVal (ρ j).val = some v := by
      intro j
      obtain ⟨ℓ, τ, -, hℓ, -⟩ := hcaps j
      rw [hR.idxToLevel] at hℓ
      exact topVal_some hσ hℓ
    refine .inr ⟨_, _, Step.closure σ k ps ret body m ρ body'
      (List.ofFn fun j => Classical.choose (hex j)) rs hbody hmono hocc hrsNodup hrs
      (by simp) ?_⟩
    intro j
    rw [List.getElem?_ofFn, dif_pos j.isLt]
    exact Classical.choose_spec (hex j)
  | appFn Δ Θ Γ Γa Γₙ Γb f Φs ρs τs args nφ nϱ nα ps τf bs hΦs hρs hτs hτsi hlenΦ hlenρ
      hlenτ hf hargs hnrb hbounds ihf iha =>
    intro Γ₀ σ hR hσ
    rcases ihf Γ₀ σ hR hσ with (⟨vf, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hRa, hvf⟩ := HasType.val_inv' hf
      rcases iha Γ₀ σ (hRa.trans hR) hσ with ⟨vs, rfl, hlen⟩ | ⟨vs, e, rest, rfl, he⟩
      · rw [List.length_map] at hlen
        rcases (canonical_forms hvf).2.2.2.2.2.2.2.2 _ _ _ _ _ _ _ rfl with
          ⟨fn, rfl⟩ | ⟨m, q, frame, body, rfl⟩
        · obtain ⟨d, hd, hps⟩ := hvf.fn_inv
          exact .inr ⟨_, _, Step.appFn σ fn d Φs ρs τs vs hd (by rw [hps, hlen])⟩
        · exact .inr ⟨_, _, Step.appClosure σ m ps.length q frame ps τf body Φs ρs τs vs hlen⟩
      · rcases he with ⟨s, rfl⟩ | ⟨σ', e', hs⟩
        · exact .inr ⟨_, _, Step.ctxAbort (.appArg vf Φs ρs τs vs rest) σ s⟩
        · exact .inr ⟨_, _, Step.ctx (.appArg vf Φs ρs τs vs rest) σ σ' e e' hs⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.appFn Φs ρs τs args) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.appFn Φs ρs τs args) σ σ' f e' hs⟩
  | appClosure Δ Θ Γ Γa Γₙ f args ps τf Φc hf hargs hnrb ihf iha =>
    intro Γ₀ σ hR hσ
    rcases ihf Γ₀ σ hR hσ with (⟨vf, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hRa, hvf⟩ := HasType.val_inv' hf
      rcases iha Γ₀ σ (hRa.trans hR) hσ with ⟨vs, rfl, hlen⟩ | ⟨vs, e, rest, rfl, he⟩
      · rcases (canonical_forms hvf).2.2.2.2.2.2.2.2 _ _ _ _ _ _ _ rfl with
          ⟨fn, rfl⟩ | ⟨m, q, frame, body, rfl⟩
        · obtain ⟨d, hd, hps⟩ := hvf.fn_inv
          exact .inr ⟨_, _, Step.appFn σ fn d [] [] [] vs hd (by rw [hps, hlen])⟩
        · exact .inr ⟨_, _, Step.appClosure σ m ps.length q frame ps τf body [] [] [] vs hlen⟩
      · rcases he with ⟨s, rfl⟩ | ⟨σ', e', hs⟩
        · exact .inr ⟨_, _, Step.ctxAbort (.appArg vf [] [] [] vs rest) σ s⟩
        · exact .inr ⟨_, _, Step.ctx (.appArg vf [] [] [] vs rest) σ σ' e e' hs⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.appFn [] [] [] args) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.appFn [] [] [] args) σ σ' f e' hs⟩
  | tuple Δ Θ Γ Γ' es τs h hsi ih =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with ⟨vs, rfl, -⟩ | ⟨vs, e, rest, rfl, he⟩
    · exact .inr ⟨_, _, Step.tupleVal σ vs⟩
    · rcases he with ⟨s, rfl⟩ | ⟨σ', e', hs⟩
      · exact .inr ⟨_, _, Step.ctxAbort (.tuple vs rest) σ s⟩
      · exact .inr ⟨_, _, Step.ctx (.tuple vs rest) σ σ' e e' hs⟩
  | array Δ Θ Γ Γ' es τ h hsi ih =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with ⟨vs, rfl, -⟩ | ⟨vs, e, rest, rfl, he⟩
    · exact .inr ⟨_, _, Step.arrayVal σ vs⟩
    · rcases he with ⟨s, rfl⟩ | ⟨σ', e', hs⟩
      · exact .inr ⟨_, _, Step.ctxAbort (.array vs rest) σ s⟩
      · exact .inr ⟨_, _, Step.ctx (.array vs rest) σ σ' e e' hs⟩
  | abort => intro Γ₀ σ hR hσ; exact .inl (.inr ⟨_, rfl⟩)
  | drop Δ Θ Γ Γd Γf π τπ τ e hπ hsi hd h ih =>
    intro Γ₀ σ hR hσ
    exact ih Γ₀ σ ((Refines.setPlaceTy_dead hd).trans hR) hσ
  | inl Δ Θ Γ Γ' τ₁ τ₂ e h hsi₁ hsi₂ ih =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · exact .inr ⟨_, _, Step.inlVal σ τ₁ τ₂ v⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.inl τ₁ τ₂) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.inl τ₁ τ₂) σ σ' e e' hs⟩
  | inr Δ Θ Γ Γ' τ₁ τ₂ e h hsi₁ hsi₂ ih =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · exact .inr ⟨_, _, Step.inrVal σ τ₁ τ₂ v⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.inr τ₁ τ₂) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.inr τ₁ τ₂) σ σ' e e' hs⟩
  | matchE Δ Θ Γ Γ' Φ₁ Φ₂ Γ₁ Γ₂ Γ₁' Γ₂' Γ'' e e₁ e₂ τl τr τ₁ τ₂ τ τdl τdr h hnrb h₁ h₂ hsd hτ
      hsi hr₁ hr₂ hu ih ih₁ ih₂ =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨-, hv⟩ := HasType.val_inv' h
      rcases (canonical_forms hv).2.2.2.2.2.2.2.1 _ _ rfl with ⟨v', rfl⟩ | ⟨v', rfl⟩
      · exact .inr ⟨_, _, Step.matchLeft σ τl τr v' e₁ e₂⟩
      · exact .inr ⟨_, _, Step.matchRight σ τl τr v' e₁ e₂⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.matchE e₁ e₂) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.matchE e₁ e₂) σ σ' e e' hs⟩
  | shift Δ Θ Γ Φ Γ' e τ τd h hsi hsd ih =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hR₁, -⟩ := HasType.val_inv' h
      obtain ⟨v', ς, σ', rfl⟩ := shape_var (hR₁.trans hR) hσ rfl
      exact .inr ⟨_, _, Step.shift v' ς σ' v⟩
    · exact .inr ⟨_, _, Step.ctxAbort .shift σ s⟩
    · exact .inr ⟨_, _, Step.ctx .shift σ σ' e e' hs⟩
  | shiftRgn Δ Θ Γ Φ Γ' L e τ h hsi hfresh ih =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hR₁, -⟩ := HasType.val_inv' h
      obtain ⟨ς, σ', rfl⟩ := shape_rgn (hR₁.trans hR) hσ rfl
      exact .inr ⟨_, _, Step.shiftRgn ς σ' v⟩
    · exact .inr ⟨_, _, Step.ctxAbort .shiftRgn σ s⟩
    · exact .inr ⟨_, _, Step.ctx .shiftRgn σ σ' e e' hs⟩
  | framed Δ Θ Γ Φ' Γ' m e τ h hsi ih =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hR₁, -⟩ := HasType.val_inv' h
      obtain ⟨ς, σ', rfl⟩ := shape_cons (hR₁.trans hR) hσ rfl
      exact .inr ⟨_, _, Step.framed ς σ' m v⟩
    · exact .inr ⟨_, _, Step.ctxAbort (.framed m) σ s⟩
    · exact .inr ⟨_, _, Step.ctx (.framed m) σ σ' e e' hs⟩
  | argsNil => intro Γ₀ σ hR hσ; exact .inl ⟨[], rfl, rfl⟩
  | argsCons Δ Θ Γ Γ₁ Γ₂ e es τ τs h t ih iht =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hR₁, -⟩ := HasType.val_inv' h
      rcases iht Γ₀ σ (hR₁.trans hR) hσ with ⟨vs, rfl, hlen⟩ | ⟨vs, e, rest, rfl, he⟩
      · exact .inl ⟨v :: vs, rfl, by simp [hlen]⟩
      · exact .inr ⟨v :: vs, e, rest, rfl, he⟩
    · exact .inr ⟨[], _, es, rfl, .inl ⟨s, rfl⟩⟩
    · exact .inr ⟨[], _, es, rfl, .inr ⟨σ', e', hs⟩⟩
  | argsRwNil => intro Γ₀ σ hR hσ; exact .inl ⟨[], rfl, rfl⟩
  | argsRwCons Δ Θ Γ Γ₁ Γ₁' Γ₂ e es τ' τ τs h hr t ih iht =>
    intro Γ₀ σ hR hσ
    rcases ih Γ₀ σ hR hσ with (⟨v, rfl⟩ | ⟨s, rfl⟩) | ⟨σ', e', hs⟩
    · obtain ⟨hR₁, -⟩ := HasType.val_inv' h
      rcases iht Γ₀ σ ((hr.refines.trans hR₁).trans hR) hσ with
        ⟨vs, rfl, hlen⟩ | ⟨vs, e, rest, rfl, he⟩
      · exact .inl ⟨v :: vs, rfl, by simp [hlen]⟩
      · exact .inr ⟨v :: vs, e, rest, rfl, he⟩
    · exact .inr ⟨[], _, es, rfl, .inl ⟨s, rfl⟩⟩
    · exact .inr ⟨[], _, es, rfl, .inr ⟨σ', e', hs⟩⟩
  | _ => trivial

end Oxide
