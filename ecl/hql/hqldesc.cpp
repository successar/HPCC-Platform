/*##############################################################################

    HPCC SYSTEMS software Copyright (C) 2012 HPCC Systems®.

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
############################################################################## */
#include "platform.h"

#include "hql.hpp"
#include "hqlexpr.hpp"
#include "hqldesc.hpp"
#include "hqlatoms.hpp"

const char * getInheritTypeText(inherit_type ihType) {
    switch(ihType) {
        case inherited : return "inherited"; break;
        case override : return "override"; break;
        case local : return "local"; break;
        default : return "unknown";
    }
    return "unknown";
}

void getFullName(StringBuffer & name, IHqlExpression * expr)
{
    IHqlScope * scope = expr->queryScope();
    if (scope)
    {
        name.append(scope->queryFullName());
    }
    else
    {
        const char * module = str(expr->queryFullContainerId());
        if (module && *module)
            name.append(module).append(".");
        name.append(expr->queryName());
    }
}

void setFullNameProp(IPropertyTree * tree, const char * prop, const char * module, const char * def)
{
    if (module && *module)
    {
        StringBuffer s;
        s.append(module).append('.').append(def);
        tree->setProp(prop, s.str());
    }
    else
        tree->setProp(prop, def);
}

void setFullNameProp(IPropertyTree * tree, const char * prop, IHqlExpression * expr)
{
    IHqlScope * scope = expr->queryScope();
    if (scope)
        tree->setProp(prop, scope->queryFullName());
    else
        setFullNameProp(tree, prop, str(lower(expr->queryFullContainerId())), str(expr->queryName()));
}

static int compareSymbolsByPosition(IInterface * const * pleft, IInterface * const * pright)
{
    IHqlExpression * left = static_cast<IHqlExpression *>(*pleft);
    IHqlExpression * right = static_cast<IHqlExpression *>(*pright);

    int startLeft = left->getStartLine();
    int startRight = right->getStartLine();
    if (startLeft != startRight)
        return startLeft < startRight ? -1 : +1;
    return stricmp(str(left->queryName()), str(right->queryName()));
}

static void setNonZeroPropInt(IPropertyTree * tree, const char * path, int value)
{
    if (value)
        tree->setPropInt(path, value);
}

static void expandRecordSymbolsMeta(IPropertyTree * metaTree, IHqlExpression * record)
{
    ForEachChild(i, record)
    {
        IHqlExpression * cur = record->queryChild(i);
        Owned<IPropertyTree> javadoc = getJavadocAnnotation(cur);

        switch (cur->getOperator())
        {
        case no_record:
            //MORE: If this is a public symbol it should be expanded, otherwise it will be elsewhere.
            expandRecordSymbolsMeta(metaTree, cur);
            break;
        case no_field:
            {
                IPropertyTree * field = metaTree->addPropTree("Field", createPTree("Field"));
                field->setProp("@name", str(cur->queryId()));
                break;
            }
        case no_ifblock:
            {
                IPropertyTree * block = metaTree->addPropTree("IfBlock", createPTree("IfBlock"));
                expandRecordSymbolsMeta(block, cur->queryChild(1));
                break;
            }
        case no_attr:
        case no_attr_link:
        case no_attr_expr:
            {
                IPropertyTree * attr = metaTree->addPropTree("Attr", createPTree("Attr"));
                attr->setProp("@name", str(cur->queryName()));
                break;
            }
        }
    }
}


void expandSymbolMeta(IPropertyTree * metaTree, IHqlExpression * expr, inherit_type ihType)
{
    IPropertyTree * def = NULL;
    if (isImport(expr))
    {
        def = metaTree->addPropTree("Import", createPTree("Import"));
        IHqlExpression * original = expr->queryBody(true);
        setFullNameProp(def, "@ref", original);
        IHqlScope * scope = expr->queryScope();
        if(scope) {
            IHqlRemoteScope * remoteScope = queryRemoteScope(scope);
            if (remoteScope) {
                def->setPropBool("@remotescope", true);
            }
        }
    }
    else
    {
        def = metaTree->addPropTree("Definition", createPTree("Definition"));
    }

    if (def)
    {
        Owned<IPropertyTree> javadoc = getJavadocAnnotation(expr);
        if (javadoc)
            def->addPropTree("Documentation", javadoc.getClear());
        IHqlNamedAnnotation * symbol = queryNameAnnotation(expr);
        def->setProp("@name", str(expr->queryId()));
        def->setPropInt("@line", expr->getStartLine());
        setFullNameProp(def, "@fullname", expr);

        if (expr->isExported())
            def->setPropBool("@exported", true);
        else if (isPublicSymbol(expr))
            def->setPropBool("@shared", true);

        def->setProp("@inherit_type", getInheritTypeText(ihType));

        if (symbol)
        {
            def->setPropInt("@start", symbol->getStartPos());
            def->setPropInt("@body", symbol->getBodyPos());
            def->setPropInt("@end", symbol->getEndPos());
            def->setProp("@source", str(expr->querySourcePath()));
        }

        if (expr->isScope() && !isImport(expr))
        {
            expandScopeMeta(def, expr);
        }
        else if (expr->isRecord())
        {
            def->setProp("Type", "record");
            expandRecordSymbolsMeta(def, expr);
        }
        else if (expr->isType())
        {
            def->setProp("Type", "type");
        }
        else {
            def->setProp("Type", "attribute");
        }
    }
}

void expandScopeMeta(IPropertyTree * meta, IHqlExpression * expr) {
    if (expr->hasAttribute(virtualAtom))
        meta->setPropBool("@virtual", true);

    if (expr->hasAttribute(interfaceAtom)){
        meta->setProp("Type", "interface");
    }
    else {
        meta->setProp("Type", "module");
    }

    IPropertyTree* scopes = meta->addPropTree("Parents", createPTree("Parents"));

    // Walk Attributes to determine inherited scopes
    ForEachChild(i, expr){
        IHqlExpression * cur = expr->queryChild(i);
        IHqlScope * curBase = cur->queryScope();
        if (curBase) {
            IPropertyTree* inherited = scopes->addPropTree("Parent", createPTree("Parent"));
            inherited->setProp("@name", str(cur->queryId()));
            inherited->setPropInt("@line", cur->getStartLine());
            setFullNameProp(inherited, "@ref", cur);
        }
    }

    expandScopeSymbolsMeta(meta, expr->queryScope());
}


void expandScopeSymbolsMeta(IPropertyTree * meta, IHqlScope * scope)
{
    if (!scope)
        return;

    HqlExprArray symbols;
    scope->getSymbols(symbols);
    symbols.sort(compareSymbolsByPosition);

    IHqlExpression * expr = queryExpression(scope);
    HqlExprArray baseSymbols;

    ForEachChild(i, expr){
        IHqlExpression * cur = expr->queryChild(i);
        IHqlScope * curBase = cur->queryScope();
        if (curBase) {
            curBase->getSymbols(baseSymbols);
        }
    }


    ForEachItemIn(i, symbols){
        IHqlExpression * curSym = &symbols.item(i);
        inherit_type ihType = local;
        ForEachItemIn(iSym, baseSymbols) {
            IHqlExpression * baseSym = &baseSymbols.item(iSym);
            if (baseSym->queryId() == curSym->queryId()) {
                ihType = inherited;
                if (baseSym->queryBody() != curSym->queryBody())
                    ihType = override;
            }
        }
        expandSymbolMeta(meta, curSym, ihType);
    }
}

void expandFunctionMeta(IPropertyTree * meta, IHqlExpression * expr)
{

    IHqlExpression * child = queryFunctionParameters(expr);
    IPropertyTree * params = meta->addPropTree("Params", createPTree("Params"));
    ForEachChild(i, child) {
        expandParamMeta(params, child->queryChild(i));
    }

    if (expr->isScope()) {
        child = expr->queryChild(0);
        if (child->isScope() && !isImport(child))
        {
            expandScopeMeta(meta, child);
        }

        return;
    }
    else if (expr->isTransform()) {
        meta->setProp("Type", "transform");
        StringBuffer ecltype;
        ecltype.append(queryOriginalRecord(expr)->queryName());
        meta->setProp("Return", ecltype);
        return;
    }
    else if (isEmbedFunction(expr)) {
        meta->setProp("Type", "embed");
    }
    else if (expr->isMacro()) {
        meta->setProp("Type", "macro");
    }
    else if (expr->isType()) {
        meta->setProp("Type", "type");
    }
    else {
        meta->setProp("Type", "function");
    }
}

void expandParamMeta(IPropertyTree * meta, IHqlExpression * cur)
{
    IPropertyTree * param = NULL;
    param = meta->addPropTree("Param", createPTree("Param"));

    if (param)
    {
        param->setProp("@name", str(cur->queryId()));
    }
}